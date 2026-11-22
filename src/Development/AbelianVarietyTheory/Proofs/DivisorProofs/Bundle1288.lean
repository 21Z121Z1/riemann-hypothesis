import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Renumber

variable {X a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [MeasurableSpace X]

def renum (E : b × a ≃ b' × a') : Matrix b' a' X ≃ᵐ Matrix b a X :=
  (MeasurableEquiv.curry b' a' X).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => X) E).symm.trans (MeasurableEquiv.curry b a X))

end Renumber

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩

def blockDiag (s : kˣ) (σ : A ⊕ A' ≃ D) : GL D k := SplitFlip.diagGL fun i => Sum.elim (fun _ => 1) (fun _ => s) (σ.symm i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] [DecidableEq A] [Fintype A']
  [DecidableEq A'] in
theorem conj_blockDiag (s : kˣ) (σ : A ⊕ A' ≃ D) (h : GL D k) (i j : A ⊕ A') :
    ((blockDiag s σ)⁻¹ * h * blockDiag s σ).val (σ i) (σ j) =
      ((Sum.elim (fun _ => 1) (fun _ => s) i : kˣ)⁻¹ : kˣ) * h.val (σ i) (σ j) *
        (Sum.elim (fun _ => 1) (fun _ => s) j : kˣ) := by
  have : ((blockDiag s σ)⁻¹).val =
    diagonal fun i => (((Sum.elim (fun _ => 1) (fun _ => s) (σ.symm i) : kˣ)⁻¹ : kˣ) : k) := rfl
  rw [Units.val_mul, Units.val_mul, this]
  simp only [blockDiag, SplitFlip.diagGL_val, mul_diagonal, diagonal_mul, Equiv.symm_apply_apply]

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in

theorem conj_mem_KO_iff {s : kˣ} (hs : (s : k) ∈ 𝒪[k]) (σ : A ⊕ A' ≃ D) {h : GL D k} (hh : h ∈ KO k D) :
    (blockDiag s σ)⁻¹ * h * blockDiag s σ ∈ KO k D ↔ ∀ i j, h.val (σ (.inr i)) (σ (.inl j)) ∈ cball s := by
  have key : ∀ x : k, ((s⁻¹ : kˣ) : k) * x ∈ 𝒪[k] ↔ x ∈ cball s := fun x => by
    rw [cball_eq_smul, Set.mem_smul_set_iff_inv_smul_mem]; rfl
  have hi := ((mem_KO_iff h).1 hh).1
  constructor
  · intro H i j
    have := ((mem_KO_iff _).1 H).1 (σ (.inr i)) (σ (.inl j))
    rw [conj_blockDiag] at this
    exact (key _).1 (by simpa using this)
  · intro H
    refine mem_KO_iff_det.2 ⟨fun i j => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := σ.surjective i
      obtain ⟨j, rfl⟩ := σ.surjective j
      rw [conj_blockDiag]
      rcases i with i | i <;> rcases j with j | j
      · simpa using hi _ _
      · simpa using mul_mem (hi _ _) hs
      · simpa using (key _).2 (H i j)
      · have : ((s⁻¹ : kˣ) : k) * h.val (σ (.inr i)) (σ (.inr j)) * s = h.val (σ (.inr i)) (σ (.inr j)) := by
          rw [mul_right_comm, Units.inv_mul, one_mul]
        simpa only [Sum.elim_inr, this] using hi _ _
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]
      exact (mem_KO_iff_det.1 hh).2

def levelJ {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D) : Subgroup (GL D k) where
  carrier := {h | h ∈ KO k D ∧ ∀ i j, h.val (σ (.inr i)) (σ (.inl j)) ∈ cball (ϖ ^ c)}
  one_mem' := ⟨one_mem _, fun i j => by simp [cball, Matrix.one_apply]⟩
  mul_mem' := fun {x y} hx hy => by
    have hs : ((ϖ ^ c : kˣ) : k) ∈ 𝒪[k] := by rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    refine ⟨mul_mem hx.1 hy.1, (conj_mem_KO_iff hs σ (mul_mem hx.1 hy.1)).1 ?_⟩
    have := mul_mem ((conj_mem_KO_iff hs σ hx.1).2 hx.2) ((conj_mem_KO_iff hs σ hy.1).2 hy.2)
    simpa only [mul_assoc, mul_inv_cancel_left] using this
  inv_mem' := fun {x} hx => by
    have hs : ((ϖ ^ c : kˣ) : k) ∈ 𝒪[k] := by rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    refine ⟨inv_mem hx.1, (conj_mem_KO_iff hs σ (inv_mem hx.1)).1 ?_⟩
    have := inv_mem ((conj_mem_KO_iff hs σ hx.1).2 hx.2)
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using this

variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

section Pair

variable {n n' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def colDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (X : Matrix (Fin n) D k) : ℂ :=
  stdDatum ν ϖ c (Xᵀ.submatrix σ id)

def rowDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (x : Matrix D (Fin n) k) : ℂ :=
  stdDatum ν ϖ c (x.submatrix σ id)

variable (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D)

omit [Fintype D] [DecidableEq D] in

theorem colDatum_eq {X : Matrix (Fin n) D k} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (h₁ : ∀ i j, X i (σ (.inl j)) = u.val i j) (h₂ : ∀ i j, X i (σ (.inr j)) ∈ cball (ϖ ^ c)) :
    colDatum ν ϖ c σ X = (((ν (GeneralLinearGroup.det u))⁻¹ : ℂˣ) : ℂ) := by
  have e : (Xᵀ.submatrix σ id).toRows₁ = u.valᵀ := by ext i j; exact h₁ j i
  have h : StdSupp ϖ c (Xᵀ.submatrix σ id) :=
    ⟨fun i j => by rw [e]; exact (mem_KO_iff_det.1 hu).1 j i, by rw [e, det_transpose]; exact (mem_KO_iff_det.1 hu).2,
      fun i j => h₂ j i⟩
  rw [colDatum, stdDatum, dif_pos h]
  congr 3
  exact Units.ext (by simp [e])

variable [MeasurableSpace k] [BorelSpace k] {m : Measure k}

def stdNormSq (q : ℝ) (c n n' : ℕ) : ℝ := (q ^ (c * n * n'))⁻¹ * glVol q n

variable {ν ϖ}

omit [MeasurableSpace k] [BorelSpace k] in

def zetaIntegrand (φ : GL (Fin n) k → ℂ) (s₀ s : ℂ) (g : GL (Fin n) k) : ℂ :=
  φ g * npow (iwAbs (absRatio k (Fin n)) (KO k (Fin n ⊕ Fin n)) (io k (Fin n) (g, 1))) (s - s₀)

end Pair

def dSplit (q n : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.Icc 1 n, (1 - (q : ℂ) ^ (-(2 * s + i)))⁻¹

section Main

variable {a a' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def swapNum (σ : Fin a ⊕ Fin a' ≃ D) : Fin a' ⊕ Fin a ≃ D := (Equiv.sumComm _ _).trans σ

def MemberClaims [MeasurableSpace k] {n : ℕ} {R C : Type} [Fintype R] [Fintype C] [MeasurableSpace (GL (Fin n) k)]
    (m : Measure k) (μ : Measure (GL (Fin n) k)) (ω : GL (Fin n) k → (Matrix R C k → ℂ) → Matrix R C k → ℂ)
    (Φ : Matrix R C k → ℂ) (c n' idx : ℕ) : Prop :=
  let q : ℕ := resCard k
  let f : ℂ → GL (Fin n) k → ℂ := zetaIntegrand (fun g => ip m (ω g Φ) Φ) ((n' : ℂ) / 2)
  ((∀ g, ip m (ω g Φ) Φ ≠ 0 → g ∈ KO k (Fin n)) ∧ (∀ g ∈ KO k (Fin n), ω g Φ = Φ) ∧
    ∀ s, Integrable (f s) μ ∧ ∫ g, f s g ∂μ = ip m Φ Φ) ∧
  ip m Φ Φ = ((((q : ℝ) ^ (c * n * n'))⁻¹ * ∏ i ∈ Finset.Icc 1 n, (1 - ((q : ℝ) ^ i)⁻¹) : ℝ) : ℂ) ∧
  dSplit q n ((n' : ℂ) / 2) = ((∏ j ∈ Finset.Ioc n' (n + n'), (1 - ((q : ℝ) ^ j)⁻¹)⁻¹ : ℝ) : ℂ) ∧
  dSplit q n ((n' : ℂ) / 2) * (idx : ℂ) * ∫ g, f ((n' : ℂ) / 2) g ∂μ = 1

end Main

section Place

open IsDedekindDomain NumberField GlobalTheory.CMVal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Place

example {n n' : ℕ} (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) :
    colDatum ν ϖ c (Equiv.refl (Fin n ⊕ Fin n')) (fromCols 1 0) = 1 := by
  rw [colDatum_eq ν ϖ c _ (one_mem _) (fun i j => rfl) fun i j => by simp [cball]]
  simp

end GlobalTheory.LocStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTorsionPoints
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.CurvSQ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthLift_transpose_mul_incl {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    (orthLift T)ᵀ * T * incl m l = 0 := by
  rw [orthLift_transpose_mul hu]; simp [incl, fromCols_mul_fromRows]

theorem mul_incl_eq {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    T * incl m l = (orthProj T)ᵀ * subGram T := by
  have hu' : IsUnit T.toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  conv_lhs => rw [← fromBlocks_toBlocks T]
  rw [incl, fromBlocks_mul_fromRows, orthProj, transpose_fromCols, fromRows_mul, orthCoeff,
    transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose, subGram,
    Matrix.mul_assoc, nonsing_inv_mul _ (show IsUnit T.toBlocks₁₁.det from hu)]
  simp

theorem mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : V) :
    mdbar (fun x => orthLift (H x)) z η = incl m l * extForm H z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
    ext (a | a) b <;> simp [orthLift, dbar_neg]
  rw [extForm, h, orthProj, fromCols_mul_fromRows, incl, fromRows_mul]
  simp

theorem quotMap_mul_mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift, quotMap, fromCols_mul_fromRows]; simp

theorem mdel_orthProj_mul_incl (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthProj (H x)) z ξ * incl m l = 0 := by
  have h : mdel (fun x => orthProj (H x)) z ξ = fromCols 0 (mdel (fun x => orthCoeff (H x)) z ξ) := by
    ext a (b | b) <;> simp [orthProj]
  rw [h, incl, fromCols_mul_fromRows]; simp

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem mContDiffAt_orthProj {k : WithTop ℕ∞} {z : V} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc := GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff h hs
  rintro a (b | b)
  exacts [contDiffAt_const, hc a b]

theorem orthProj_mul_covDel_orthLift (h : IsHermFrame U H)
    (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) {x : V} (hx : x ∈ U) (ξ : V) :
    orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) = 0 := by
  have hL : MContDiffAt 1 (fun y => orthLift (H y)) x :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.one hx) (hs x hx)
  have hA : MContDiffAt 1 (fun y => (orthLift (H y))ᵀ * H y) x := hL.transpose.mul (h.one hx)
  have hB : MContDiffAt 1 (fun _ : V => incl m l) x := mContDiffAt_const _
  have e0 : mdel (fun y => (orthLift (H y))ᵀ * H y * incl m l) x ξ = 0 := by
    rw [mdel_congr (B := fun _ => (0 : Matrix l m ℂ)) (mem_of_superset (h.isOpen.mem_nhds hx)
      fun y hy => orthLift_transpose_mul_incl (hs y hy)), mdel_const]
  rw [mdel_mul hA hB, mdel_const, Matrix.mul_zero, zero_add, mdel_mul hL.transpose (h.one hx),
    mdel_transpose, ← conn_transpose_mul (h.isUnit x hx)] at e0
  have e1 : (orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ +
      conn H x ξ * orthLift (H x)))ᵀ * subGram (H x) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, ← mul_incl_eq (hs x hx), ← e0, transpose_add,
      transpose_mul]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 := congrArg (· * (subGram (H x))⁻¹) e1
  simp only [Matrix.mul_assoc, mul_nonsing_inv _ (hs x hx), Matrix.mul_one, Matrix.zero_mul] at e2
  exact transpose_eq_zero.1 e2

theorem covDel_orthLift (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
    {x : V} (hx : x ∈ U) (ξ : V) :
    mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x) =
      orthLift (H x) * blockQQ (H x) (conn H x ξ) := by
  calc _ = (incl m l * orthProj (H x) + orthLift (H x) * quotMap m l) *
        (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) := by
          rw [incl_mul_orthProj_add, Matrix.one_mul]
    _ = _ := by
      rw [Matrix.add_mul, Matrix.mul_assoc, orthProj_mul_covDel_orthLift h hs hx,
        Matrix.mul_zero, zero_add, Matrix.mul_assoc, Matrix.mul_add,
        quotMap_mul_mdel_orthLift, zero_add, blockQQ, Matrix.mul_assoc]

theorem blockSQ_curv_eq_covDelAnti_extForm {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL2 : MContDiffAt 2 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.two hz) hsz
  have hL1 : MContDiffAt 1 (fun x => orthLift (H x)) z := hL2.of_le one_le_two
  have hP1 : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj (h.one hz) hsz
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := (h.two hz).conn hu (by norm_num) ξ
  have hdL : MContDiffAt 1 (fun x => mdel (fun y => orthLift (H y)) x ξ) z :=
    hL2.mdel (by norm_num) ξ
  have hbL : MContDiffAt 1 (fun x => mdbar (fun y => orthLift (H y)) x η) z :=
    hL2.mdbar (by norm_num) η
  have hM : MContDiffAt 1 (fun x => blockQQ (H x) (conn H x ξ)) z :=
    ((mContDiffAt_const _).mul hc).mul hL1
  have he : (fun x => mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) =ᶠ[𝓝 z]
      fun x => orthLift (H x) * blockQQ (H x) (conn H x ξ) :=
    mem_of_superset (h.isOpen.mem_nhds hz) fun x hx => covDel_orthLift h hs hx ξ
  have F1 := mdbar_congr he η
  rw [mdbar_add hdL (hc.mul hL1), mdbar_mdel hL2, mdbar_mul hc hL1, mdbar_mul hL1 hM] at F1
  have cS : conn (gramS H) z ξ = blockSS (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_sub hu hsz ξ
  have cQ : conn (gramQ H) z ξ = blockQQ (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_quot (h.one hz) hu hsz ξ
  have kB : mdbar (fun x => orthLift (H x)) z η =
      incl m l * (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := mdbar_orthLift H z η
  have k1 : orthProj (H z) * mdbar (fun x => conn H x ξ) z η * orthLift (H z) =
      orthProj (H z) * mdbar (fun x => orthLift (H x)) z η * blockQQ (H z) (conn H z ξ)
        - orthProj (H z) * mddbar (fun x => orthLift (H x)) z ξ η
        - orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η := by
    have e := congrArg (orthProj (H z) * ·) F1
    simp only [Matrix.mul_add] at e
    rw [← Matrix.mul_assoc (orthProj (H z)) (orthLift (H z)), orthProj_mul_orthLift,
      Matrix.zero_mul, zero_add] at e
    simp only [Matrix.mul_assoc]
    rw [← e]
    abel
  have k2 : mdel (fun x => orthProj (H x)) z ξ * mdbar (fun x => orthLift (H x)) z η = 0 := by
    rw [kB, ← Matrix.mul_assoc, mdel_orthProj_mul_incl, Matrix.zero_mul]
  have k3 : orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η =
      orthProj (H z) * conn H z ξ * incl m l *
        (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := by
    conv_lhs => rw [kB]
    simp only [Matrix.mul_assoc]
  simp only [covDelAnti, homDel, extForm]
  rw [mdel_mul hP1 hbL, mdel_mdbar hL2, k2, add_zero, cS, cQ, blockSQ, curv, Matrix.mul_neg,
    Matrix.neg_mul, k1, k3, blockSS]
  simp only [Matrix.mul_assoc]
  abel

end GlobalTheory.CurvSQ
end
end

