import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

open Matrix

namespace GlobalTheory.BadCount.WtPsi

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (c : ZMod g)

theorem posN_lt {a : ℕ} (h : a < N) : posN 0 N a = a := by
  unfold posN; simp [h]

theorem sdg_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    ∑ i ∈ Finset.range (N - 1), entN (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u *
      diagonal (fun i : Fin N => tN 0 N c i)) i (i + 1) = c * ∑ i ∈ Finset.range (N - 1), entN u i (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [entN_conj, pair 0 N c hc (by rw [posN_lt (by omega), posN_lt (by omega)])]

theorem uniUp_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    IsUniUp (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u * diagonal (fun i : Fin N => tN 0 N c i)) ↔ IsUniUp u := by
  have h := PJ_conj 0 N c hc u
  unfold PJ at h
  have hv : ∀ M : Matrix (Fin N) (Fin N) (ZMod g), ∀ a, N ≤ a → a < N → entN M a N = 0 :=
    fun _ a h1 h2 => absurd h2 (by omega)
  exact ⟨fun x => (h.1 ⟨x, hv _⟩).1, fun x => (h.2 ⟨x, hv _⟩).1⟩

theorem eU_conj (hc : c ≠ 0) (ψ : AddChar (ZMod g) ℂ) :
    haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
    MonoidAlgebra.single (T 0 N c hc) 1 * eU g N ψ * MonoidAlgebra.single (T 0 N c hc)⁻¹ 1 =
      eU g N (ψ.mulShift c) := by
  classical
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  unfold eU eDat
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Finset.sum_nbij' (fun u => T 0 N c hc * u * (T 0 N c hc)⁻¹) (fun v => (T 0 N c hc)⁻¹ * v * T 0 N c hc)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    show IsUniUp ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [← uniUp_conj c hc, ← T_conj_val 0 N c hc]
    have e : (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc = u := by group
    rw [e]; exact hu
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    show IsUniUp (((T 0 N c hc)⁻¹ * v * T 0 N c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [T_conj_val, uniUp_conj c hc]; exact hv
  · intro u _; group
  · intro v _; group
  · intro u hu
    have e : (u : GL (Fin N) (ZMod g)) = (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc := by group
    have hφ : ∑ i ∈ Finset.range (N - 1), entN (u : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) =
        c * ∑ i ∈ Finset.range (N - 1),
          entN ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) := by
      conv_lhs => rw [e]
      rw [T_conj_val, sdg_conj c hc]
    rw [hφ, AddChar.mulShift_apply]

end GlobalTheory.BadCount.WtPsi

namespace GlobalTheory.BadCount

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr GlobalTheory.BadCount.WtPsi

theorem wtOf_eUk_indep : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 →
    ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  intro D k ψ ψ' h h' f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, hc0, rfl⟩ := exists_shift ψ ψ' h h'
  have hconj : eUk D k (ψ.mulShift c) =
      MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
    unfold eUk
    exact (eU_conj c hc0 ψ).symm
  have h1 : (eUk D k (ψ.mulShift c) * D.ntypes.eSer k f).coeff 1 = (eUk D k ψ * D.ntypes.eSer k f).coeff 1 := by
    rw [hconj]
    have e1 : MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 *
        D.ntypes.eSer k f = MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * (eUk D k ψ * D.ntypes.eSer k f) *
        MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
      rw [mul_assoc _ (MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1) (D.ntypes.eSer k f), ← D.ntypes.eSer_central,
        mul_assoc, mul_assoc, mul_assoc]
    rw [e1, tau_conj]
  have h2 : (eUk D k (ψ.mulShift c)).coeff 1 = (eUk D k ψ).coeff 1 := by
    rw [hconj, tau_conj]
  unfold wtOf
  rw [h1, h2]

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTrace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocSymp

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] (σL : L →+* L) {α β : Type} [Fintype α] [Fintype β]
    (X Y : Matrix α β L) (A : Matrix α α L) (B : Matrix β β L) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j * A i k * B j l * σL (Y k l)) =
      Matrix.trace (A * Y.map σL * Bᵀ * Xᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_coords {L : Type} [CommRing L] (σL : L →+* L) {n d : ℕ}
    (PV A : Matrix (Fin n) (Fin n) L) (PW B : Matrix (Fin d) (Fin d) L) (x y : Matrix (Fin d) (Fin n) L) :
    Matrix.trace (A * (PV * yᵀ * PWᵀ).map σL * Bᵀ * (PV * xᵀ * PWᵀ)ᵀ) =
      Matrix.trace ((PVᵀ * A * PV.map σL) * (y.map σL)ᵀ * (PWᵀ * B * PW.map σL)ᵀ * x) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm PVᵀ]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_inclR {L : Type} [Field L] (ι : L →+ AE F E) (v : Pl F)
    (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (a : L) (e : E) :
    ι a * inclR (F := F) (AF F) e = ι (a * GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e)) := by
  have hat : ∃ z, ι z = ι 1 * inclR (F := F) (AF F) e := by
    refine (hAt _).1 fun u hu => ?_
    have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
    rw [← smul_mul_assoc, h1, zero_mul]
  rw [hmul, GlobalTheory.InertLocFrame.pre_spec ι hat, ← mul_assoc, ← hmul, mul_one]

end GlobalTheory.InertLocSymp

open GlobalTheory.InertLocSymp in

theorem GlobalTheory.InertLocSymp.psi_symp_eq :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl F) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  intro F E _ _ _ _ _ σ B v n d X W L _ _ ϖ σL q δ ψL ι _ hδ hinj hAt hmul hσ hψ PV JS PW JT hGV hGW x y
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hδ; exact zero_ne_one hδ.1

  have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      ι (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) := by
    simp only [hTens, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.InertLocFrame.xm_apply, incM, Matrix.map_apply, ← hσ]
    rw [mul_inclR ι v hAt hmul, mul_inclR ι v hAt hmul, ← hmul]
    rfl

  have hS : (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) =
      -GlobalTheory.Hk3.locH σL δ JS JT x y := by
    rw [quadruple_sum_eq_trace_transpose_mul, trace_coords]
    have e1 : (PV : Matrix (Fin n) (Fin n) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι X.J * (PV : Matrix (Fin n) (Fin n) L).map σL =
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := hGV.symm
    have e2 : ((PW : Matrix (Fin d) (Fin d) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι W.J * (PW : Matrix (Fin d) (Fin d) L).map σL)ᵀ =
        -δ • (JT : Matrix (Fin d) (Fin d) L) := by
      rw [hGW, smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]; rfl
    rw [e1, e2, GlobalTheory.Hk3.locH, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm _ x]
    simp only [Matrix.mul_assoc]; ring
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h1 : (2 : AF F) • ι 1 = 0 := by
      rw [two_smul, ← map_add, one_add_one_eq_two, h, map_zero]
    have : ι 1 = 0 := by
      rw [← one_smul (AF F) (ι 1), ← invOf_mul_self (2 : AF F), mul_smul, h1, smul_zero]
    exact one_ne_zero (hinj (this.trans (map_zero ι).symm))
  haveI : NeZero (2 : L) := ⟨h2⟩
  set z := GlobalTheory.Hk3.locH σL δ JS JT x y
  have hhalf : ⅟(2 : AF F) • ι z = ι (z / 2) := by
    have : ι z = (2 : AF F) • ι (z / 2) := by
      rw [two_smul, ← map_add, add_halves]
    rw [this, smul_smul, invOf_mul_self, one_smul]
  have hsymp : ⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      Algebra.trace (AF F) (AE F E) (ι (z / 2)) := by
    rw [symp, hT, hS, map_neg, neg_one_mul, neg_neg, ← smul_eq_mul, ← LinearMap.map_smul, hhalf]
  rw [hsymp, hψ, map_div₀, map_ofNat, add_div]
end
end

