import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0107
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
section
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]
  by_cases h : coeff m F = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEvenStatement
section
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_minus_signs_half_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.m → 0 < G.ga → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧ (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 := by
  first | exact @GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | exact GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | (intros; apply GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Finite

variable {F : Type} [Field F] {N : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def IsCuspLevi (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) : Prop :=
  ∀ c : Fin N → ℕ, (∃ i j, b i = b j ∧ c i ≠ c j) → ∀ x : W,
    (∀ m : Parabolic.levi F b, (m : GL (Fin N) F) ∈ FiniteGL.unipRadical F c → μ m x = x) → x = 0

def IsCuspPair (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) : Prop :=
  μ.IsIrreducible ∧ IsCuspLevi b μ

def Conj (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (b' : Fin N → ℕ) (μ' : Representation ℂ (Parabolic.levi F b') W') : Prop :=
  ∃ w : Equiv.Perm (Fin N), (∀ i j, b' (w i) = b' (w j) ↔ b i = b j) ∧ ∃ φ : W ≃ₗ[ℂ] W',
    ∀ (m : Parabolic.levi F b) (m' : Parabolic.levi F b') (x : W),
      (m' : GL (Fin N) F) = Parabolic.permGL F w * m * (Parabolic.permGL F w)⁻¹ → φ (μ m x) = μ' m' (φ x)

def HasChar (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) (θ : Fˣ →* ℂˣ) : Prop :=
  ∃ i, (∀ j, b j = b i → j = i) ∧ ∀ m : Parabolic.levi F b,
    (∀ p q, (p ≠ i ∨ q ≠ i) → (m : GL (Fin N) F).val p q = (1 : Matrix (Fin N) (Fin N) F) p q) →
      ∀ x, μ m x = (θ (Matrix.GeneralLinearGroup.det (m : GL (Fin N) F)) : ℂ) • x

def IsCharFin (ρ : Representation ℂ (GL (Fin N) F) V) (θ : Fˣ →* ℂˣ) : Prop :=
  N = 1 ∧ ∀ g y, ρ g y = (θ (Matrix.GeneralLinearGroup.det g) : ℂ) • y

def Link (τ : Representation ℂ (GL (Fin N) F) V) (τ' : Representation ℂ (GL (Fin N) F) V') : Prop :=
  ∃ (b : Fin N → ℕ) (φ : (Parabolic.hcRes b τ).IntertwiningMap (Parabolic.hcRes b τ')), φ ≠ 0

def Occurs (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (τ : Representation ℂ (GL (Fin N) F) V) : Prop :=
  Parabolic.Embeds μ (Parabolic.hcRes b τ)

end Finite

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

abbrev LiftSp (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Type :=
  IndSp (part r t) ((extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)).comp
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)

def evAt (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) (g : GL (Fin (r + t)) k) :
    LiftSp t σ χW χV →ₗ[ℂ] V where
  toFun f := TensorProduct.rid ℂ V (f.1.1 g)
  map_add' f f' := map_add (TensorProduct.rid ℂ V) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := map_smul (TensorProduct.rid ℂ V) c (f.1.1 g)

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

theorem evAt_apply (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g f = TensorProduct.rid ℂ V (f.1.1 g) := rfl

theorem evAt_lift (g x : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g (liftRep t σ χW χV x f) = evAt t σ χW χV (g * x) f := rfl

theorem eq_zero_of_evAt (f : LiftSp t σ χW χV) (h : ∀ g, evAt t σ χW χV g f = 0) : f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hg := h g
  rw [evAt_apply] at hg
  exact (LinearEquiv.map_eq_zero_iff _).mp hg

private theorem rid_extTensor_twist_detRep_eq_smul (g : GL (Fin r) k × GL (Fin t) k) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW) g x) =
      ((detChar (Fin r) (χW * χV⁻¹) g.1 * detChar (Fin t) χW g.2 : ℂˣ) : ℂ) •
        σ g.1 (TensorProduct.rid ℂ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    simp only [extTensor_tmul, twist_apply, detRep, ofChar_apply, TensorProduct.rid_tmul, map_smul,
      Units.val_mul, mul_smul]
    simp only [smul_smul]
    congr 1
    ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem evAt_parab (p : parab k (part r t)) (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV (p * g) f =
      ((deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (part r t) p) *
        detChar (Fin r) (χW * χV⁻¹) (leviProj k (part r t) p false) *
        detChar (Fin t) χW (leviProj k (part r t) p true) : ℂˣ) : ℂ) •
        σ (leviProj k (part r t) p false) (evAt t σ χW χV g f) := by
  rw [evAt_apply, evAt_apply, parInd_law, map_smul]
  erw [rid_extTensor_twist_detRep_eq_smul]
  rw [← mul_smul, mul_assoc, Units.val_mul (deltaHalf k _ _)]
  rfl

theorem evAt_parab_ne_zero (p : parab k (part r t)) (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV)
    (h : evAt t σ χW χV (p * g) f ≠ 0) : evAt t σ χW χV g f ≠ 0 := by
  intro hg
  apply h
  rw [evAt_parab, hg, map_zero, smul_zero]

private theorem valuation_det_incl_eq_one {n : ℕ} (a : GL (Fin n) 𝒪[k]) :
    valuation k ((Matrix.GeneralLinearGroup.det (incl k n a) : kˣ) : k) = 1 := by
  rw [show incl k n a = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) a from rfl,
    Matrix.GeneralLinearGroup.map_det]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  exact (Valuation.integer.integers _).one_of_isUnit (Units.isUnit _)

theorem detChar_incl {n : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) (a : GL (Fin n) 𝒪[k]) :
    detChar (Fin n) χ (incl k n a) = 1 := by
  rw [detChar_apply]
  exact h _ (valuation_det_incl_eq_one a)

theorem evAt_parab_int (hu : IsUnram (χW * χV⁻¹)) (p : GL (Fin (r + t)) k) (a : GL (Fin r) 𝒪[k])
    (d : GL (Fin t) 𝒪[k])
    (ha : ∀ i j, p.val (Fin.castAdd t i) (Fin.castAdd t j) = (incl k r a).val i j)
    (hd : ∀ i j, p.val (Fin.natAdd r i) (Fin.natAdd r j) = (incl k t d).val i j)
    (hc : ∀ i j, p.val (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV (p * g) f =
      (detChar (Fin t) χW (incl k t d) : ℂ) • σ (incl k r a) (evAt t σ χW χV g f) := by
  have hp : p ∈ parab k (part r t) := by
    rw [mem_parab_two]
    intro j i
    exact hc j i
  have h1 := evAt_parab (σ := σ) (χW := χW) (χV := χV) ⟨p, hp⟩ g f
  have hL0 : leviProj k (part r t) ⟨p, hp⟩ false = incl k r a := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [leviProj_apply]
    exact ha i j
  have hL1 : leviProj k (part r t) ⟨p, hp⟩ true = incl k t d := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [leviProj_apply]
    exact hd i j
  have hδ : deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (part r t) ⟨p, hp⟩) = 1 := by
    rw [deltaHalf_apply]
    apply Finset.prod_eq_one
    intro x _
    apply isUnram_absPow
    cases x
    · rw [hL0]
      exact valuation_det_incl_eq_one a
    · rw [hL1]
      exact valuation_det_incl_eq_one d
  rw [show p * g = ((⟨p, hp⟩ : parab k (part r t)) : GL (Fin (r + t)) k) * g from rfl, h1, hδ, hL0, hL1,
    detChar_incl hu a]
  simp only [one_mul]

def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

theorem red_surjective (n : ℕ) : Function.Surjective (red k n) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪[k])) (g.val i j)
  have hM : M.map (IsLocalRing.residue 𝒪[k]) = g.val := by
    ext i j
    exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _
  have hdet : IsUnit M.det := by
    apply IsUnit.of_map (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact Matrix.isUnits_det_units g
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [red_val]
  exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _

theorem mem_fixed_KOne {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {v : V} :
    v ∈ fixed π (KOne k (Fin n)) ↔ ∀ a : GL (Fin n) 𝒪[k], red k n a = 1 → π (incl k n a) v = v := by
  rw [GlobalTheory.Parabolic.mem_fixed]
  constructor
  · intro hv a ha
    exact hv _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem mem_fixed_KO {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {v : V} :
    v ∈ fixed π (KO k (Fin n)) ↔ ∀ a : GL (Fin n) 𝒪[k], π (incl k n a) v = v := by
  rw [GlobalTheory.Parabolic.mem_fixed]
  constructor
  · intro hv a
    exact hv _ ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    exact h a

def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)

theorem nice_one : Nice r t 1 ∅ := by
  refine ⟨fun i _ => rfl, fun i hi => ?_, fun _ => rfl⟩
  simp at hi

end Local

end GlobalTheory.TypeDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColAddFixedOfStable
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem rename_swap_matRep_one_right {n n' : ℕ} (g : GL (Fin n) ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (matRep n n' (g, 1) v) =
      rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (rename Prod.swap v) := by
  have : (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ).comp (rename Prod.swap) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply]
  exact DFunLike.congr_fun this v

theorem rename_swap_colAdd {n n' : ℕ} (l j : Fin n) (c : ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (colAdd ℂ l j c v) =
      Polynomial.eval (C c) (rowGen ℂ l j (rename Prod.swap v)) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp [colAdd, rowGen]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : s = j <;> simp [colAdd, rowGen, h, mul_comm (C c)]

theorem rowGen_coeff_zero_eq {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    (rowGen ℂ a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowGen]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : v.1 = b <;> simp [rowGen, h]

theorem exists_colAdd_fixed_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c v = v := by
  have hinj : Function.Injective
      (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')) :=
    rename_injective _ Prod.swap_injective
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n') ℂ) :=
    N.map (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).toLinearMap
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    exact ⟨_, hst (unitaryIncl n t) f hf, rename_swap_matRep_one_right (unitaryIncl n t) f⟩
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hN (Submodule.map_injective_of_injective hinj
    (e.trans (Submodule.map_bot _).symm))
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hcl hne
  refine ⟨v, hv, fun e => hv0 (by rw [e, map_zero]), fun l j hlj c => hinj ?_⟩
  have hC : rowGen ℂ l j (rename Prod.swap v) = Polynomial.C (rename Prod.swap v) := by
    ext1 k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [rowGen_coeff_zero_eq, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hk.ne']
      exact hkill l j hlj k hk
  rw [rename_swap_colAdd, hC, Polynomial.eval_C]

end GlobalTheory.GLDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMapNablaSqPad
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open scoped Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def dropCols (r m : ℕ) : MvPolynomial (Fin r × Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
  aeval fun v => if h : v.2.val < m then X (v.1, ⟨v.2.val, h⟩) else 0

theorem dropCols_rowAct (r m : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    dropCols r m (rowAct ℂ g f) = rowAct ℂ g (dropCols r m f) := by
  have : (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]
  exact DFunLike.congr_fun this f

theorem dropCols_lpMinor (r m s : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    dropCols r m (lpMinor ℂ s hr hr) = lpMinor ℂ s hr hm := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext1 p q
  have hq : q.val < m := lt_of_lt_of_le q.2 hm
  simp [dropCols, hq, Fin.castLE]

theorem dropCols_hw (r m : ℕ) (h : m ≤ r) (ν : Fin m → ℕ) :
    dropCols r m (hw ℂ (le_refl r) (rowNu ν)) = hw ℂ h ν := by
  unfold hw
  rw [map_prod]
  symm
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < m := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    simp [rowNu, hs']
  · intro s _
    rw [map_pow]
    have e : nuNext (rowNu (r := r) ν) (Fin.castLE h s) = nuNext ν s := by
      simp only [nuNext, rowNu, Fin.val_castLE]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · omega
      · rfl
    have e' : rowNu (r := r) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    rw [e, e']
    congr 1
    exact (dropCols_lpMinor r m (s.val + 1) _ _).symm

theorem pad_detShift_nonneg {m : ℕ} (r : ℕ) (a : Part m) : 0 ≤ (pad r a).detShift := by
  unfold DomWeight.detShift
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem pad_natW_add {m : ℕ} (r : ℕ) (a : Part m) (i : Fin r) :
    (pad r a).natW i + (pad r a).detShift.toNat = rowNu a.1 i := by
  have h0 := pad_detShift_nonneg r a
  have h1 : (pad r a).detShift ≤ (pad r a).w i := by
    unfold DomWeight.detShift
    rw [dif_pos i.pos]
    apply (pad r a).anti
    rw [Fin.le_def]
    have := i.2
    simp only
    omega
  have h2 : (pad r a).w i = (rowNu (r := r) a.1 i : ℕ) := rfl
  simp only [DomWeight.natW]
  omega

theorem exists_map_nablaSq_pad : ∀ (r m : ℕ) (h : m ≤ r) (a : Part m), ∃ j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ, (∀ (g : GL (Fin r) ℂ) (f : nablaSq ℂ r (pad r a)), j (sqRep ℂ r (pad r a) g f) = rowAct ℂ (g : Matrix (Fin r) (Fin r) ℂ)ᵀ (j f)) ∧ ∀ f : nablaSq ℂ r (pad r a), (f : MvPolynomial (Fin r × Fin r) ℂ) = extremal ℂ r (pad r a) → j f = hw ℂ h a.1 := by
  intro r m h a
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)
  let j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
    (dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ
      (nablaSq ℂ r (pad r a)).subtype
  have hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f) := fun _ => rfl
  refine ⟨j, fun g f => ?_, fun f hf => ?_⟩
  · rw [hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc,
      mul_smul_comm, Matrix.det_transpose]
    simp [detPow]
  · rw [hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]
    congr 2
    funext i
    have := pad_natW_add r a i
    rwa [hc, Int.toNat_natCast] at this

end GlobalTheory.GLDuality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEvenStatement
section
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_param_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  first | exact @GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | exact GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | (intros; apply GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 <;> assumption)
end

