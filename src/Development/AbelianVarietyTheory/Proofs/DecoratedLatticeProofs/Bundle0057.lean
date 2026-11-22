import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLiftedFlagBasisReduceModLevel

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditionsStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCongruence_iff_flag_conditions : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → (K2cong I g e0 z0 bw x ↔ FlagCond (ZMod' I g) ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | exact GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | (intros; apply GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MuMaxNonposOfLcvNonneg
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData in

theorem muMax_nonpos_of_lcv_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K), (∀ v, IsUnit (A.X v).det) → A.L.FG → A.L ≠ ⊥ → (∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N ≠ ⊥ → 0 ≤ (Formalism.L2.GlobalTheoryTheory.HLatOps.withL A N).lcv) → A.muMax ≤ 0 := by
  intro K _ _ _ _ A hX hL hL0 h
  unfold HLat.muMax
  refine muMaxDef_le A.b A.X hL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := fg_of_le hL hQ
  have hl := h Q hQ hQ0
  simp only [HLat.lcv, Formalism.L2.GlobalTheoryTheory.HLatOps.withL] at hl
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos'
  have h2 : (0 : ℝ) < 2 / (Module.finrank ℚ K : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (ht A.b A.X Q) := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_pos_of_neg h2 hc
    linarith
  rw [muDef_eq_log A.b A.X hX hQfg hQ0]
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hr : (0 : ℝ) < (rkK Q : ℝ) := by exact_mod_cast rkK_pos hQ0
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdNormGramRLeProdGramDet
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

namespace GramPlacesCS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem map_gramR {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K) (σ : K →+* ℂ) :
    σ (gramR G e) =
      ((StepBAux.fmat (Rb.tw σ) e)ᴴ * G.map σ * StepBAux.fmat σ e).det := by
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, StepBAux.fmat, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum,
    map_mul, Rb.tw_apply, Complex.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [NumberField K] [StarRing K] in

theorem det_conjugate {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K)
    (φ : K →+* ℂ) :
    ((StepBAux.fmat (ComplexEmbedding.conjugate φ) e)ᴴ * G.map (ComplexEmbedding.conjugate φ) *
        StepBAux.fmat (ComplexEmbedding.conjugate φ) e).det =
      starRingEnd ℂ (((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det) := by
  have hE : StepBAux.fmat (ComplexEmbedding.conjugate φ) e =
      (StepBAux.fmat φ e).map (starRingEnd ℂ) := by
    ext i a; simp [StepBAux.fmat, ComplexEmbedding.conjugate_coe_eq]
  have hG : G.map (ComplexEmbedding.conjugate φ) = (G.map φ).map (starRingEnd ℂ) := by
    ext i a; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hE, hG, Rb.conjT_map_conj, ← Matrix.map_mul, ← Matrix.map_mul,
    RingHom.map_det, RingHom.mapMatrix_apply]

theorem gram_eq (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    gram X v e =
      (StepBAux.fmat v.embedding e)ᴴ * G.map v.embedding * StepBAux.fmat v.embedding e := by
  rw [StepBAux.gram_eq_fmat, StepBAux.met, (hX.2 v).2]

theorem gram_mk_re (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (φ : K →+* ℂ) :
    (gram X (InfinitePlace.mk φ) e).det.re =
      ((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det.re := by
  rw [gram_eq K0 G X hX]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, det_conjugate, Complex.conj_re]

theorem map_posDef (K0 : Subfield K) {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (v : InfinitePlace K) : (G.map v.embedding).PosDef := by
  rw [← (hX.2 v).2]
  exact Rb.metMat_posDef X v (hX.2 v).1

theorem gram_det_re_nonneg (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  rw [gram_eq K0 G X hX]
  have h := ((map_posDef K0 G X hX v).posSemidef.conjTranspose_mul_mul_same
    (StepBAux.fmat v.embedding e)).det_nonneg
  exact (Complex.le_def.mp h).1

theorem place_sq_le (K0 : Subfield K) (hK0 : IsCMSub K0) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    ‖v.embedding (gramR G e)‖ ^ 2 ≤ (gram X (Rb.plc v) e).det.re * (gram X v e).det.re := by
  have h := determinant_cauchy_schwarz n j _ (map_posDef K0 G X hX v)
    (StepBAux.fmat (Rb.tw v.embedding) e)ᴴ (StepBAux.fmat v.embedding e)ᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [map_gramR, Rb.plc, gram_mk_re K0 G X hX, Rb.Hmap_tw K0 hK0 G hX.1, gram_eq K0 G X hX]
  exact h

end GramPlacesCS

open GramPlacesCS in

theorem prod_norm_gramR_le_prod_gram_det :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n j : ℕ) (G : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 G X → ∀ e : Fin j → Fin n → K,
      ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ≤
        ∏ v : InfinitePlace K, (gram X v e).det.re := by
  intro K _ _ _ K0 hK0 n j G X hX e
  have hperm : ∏ v : InfinitePlace K, (gram X (Rb.plc v) e).det.re =
      ∏ v : InfinitePlace K, (gram X v e).det.re :=
    Equiv.prod_comp (Function.Involutive.toPerm _ Rb.plc_plc) (fun v => (gram X v e).det.re)
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
    calc (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2
        = ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ^ 2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ v : InfinitePlace K, ((gram X (Rb.plc v) e).det.re * (gram X v e).det.re) :=
        Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => place_sq_le K0 hK0 G X hX e v)
      _ = (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
        rw [Finset.prod_mul_distrib, hperm, sq]
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun v _ => gram_det_re_nonneg K0 G X hX e v) two_ne_zero).mp hsq

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatHermHermUnitAniso
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ratHerm_herm_unit_aniso : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K)
    (v0 : InfinitePlace K), IsConjAt v0 → ∀ (n j : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 G X →
    Gᴴ = G ∧ IsUnit G.det ∧ ∀ e : Fin j → Fin n → K, LinearIndependent K e → gramR G e ≠ 0 := by
  intro K _ _ _ K0 v0 hc n j G X hG
  set s0 : K →+* ℂ := v0.embedding with hs0
  obtain ⟨hXu, hXG⟩ := hG.2 v0
  set Y : Matrix (Fin n) (Fin n) ℂ := (X v0)⁻¹ with hY
  have hYu : IsUnit Y.det := Matrix.isUnit_nonsing_inv_det _ hXu
  have hYinj : Function.Injective Y.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hYu)
  have hpos : (G.map s0).PosDef := by
    rw [← hXG]; exact Matrix.PosDef.conjTranspose_mul_self _ hYinj
  have hstar : ∀ {m d : ℕ} (E : Matrix (Fin m) (Fin d) K), (Eᴴ).map s0 = (E.map s0)ᴴ :=
    fun E => Formalism.L2.DIV.map_conjTranspose' s0 E (fun i a => hc (E i a))
  have hmapinj : ∀ {m d : ℕ} {A B : Matrix (Fin m) (Fin d) K}, A.map s0 = B.map s0 → A = B := by
    intro m d A B h
    ext i k
    exact s0.injective (congrFun (congrFun h i) k)
  refine ⟨?_, ?_, ?_⟩
  · apply hmapinj
    rw [hstar, hpos.1.eq]
  · rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : s0 G.det = (G.map s0).det := RingHom.map_det s0 G
    rw [h0, map_zero] at h1
    exact hpos.det_pos.ne' h1.symm
  · intro e he
    set E : Matrix (Fin n) (Fin j) K := Matrix.of fun i b => e b i with hE
    have hEinj : Function.Injective E.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact he
    have hgram : (Matrix.of fun a b => star (e a) ⬝ᵥ G.mulVec (e b)) = Eᴴ * G * E := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hE, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hPD : ((E.map s0)ᴴ * G.map s0 * E.map s0).PosDef :=
      hpos.conjTranspose_mul_mul_same (Formalism.L2.DIV.map_inj s0 E hEinj)
    unfold gramR
    rw [hgram]
    intro h0
    have h1 : s0 (Eᴴ * G * E).det = ((Eᴴ * G * E).map s0).det := RingHom.map_det s0 _
    rw [h0, map_zero, Matrix.map_mul, Matrix.map_mul, hstar] at h1
    exact hPD.det_pos.ne' h1.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDualStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagDual.unipSym_of_dual | exact GlobalTheory.FlagDual.unipSym_of_dual | (intros; apply GlobalTheory.FlagDual.unipSym_of_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDualStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) → FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagCase.flagCond_dual_unipSym | exact GlobalTheory.FlagCase.flagCond_dual_unipSym | (intros; apply GlobalTheory.FlagCase.flagCond_dual_unipSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLiftedFlagBasisReduceModLevelStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  first | exact @GlobalTheory.FlagUnit.unitary_reduce | exact GlobalTheory.FlagUnit.unitary_reduce | (intros; apply GlobalTheory.FlagUnit.unitary_reduce <;> assumption)
end

