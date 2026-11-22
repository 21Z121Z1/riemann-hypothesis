import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Ind

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

def Keeps (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Prop := ∀ t, q t = 0 → q (L t) = 0

def indOp (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Module.End ℂ P :=
  if h : Function.Surjective q ∧ Keeps q L then
    (q.quotKerEquivOfSurjective h.1).toLinearMap ∘ₗ
      ((LinearMap.ker q).mapQ (LinearMap.ker q) L fun t ht => LinearMap.mem_ker.2 (h.2 t (LinearMap.mem_ker.1 ht))) ∘ₗ
        (q.quotKerEquivOfSurjective h.1).symm.toLinearMap
  else 0

theorem indOp_apply {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L) (t : T) :
    indOp q L (q t) = q (L t) := by
  have e : (q.quotKerEquivOfSurjective hq).symm (q t) = Submodule.Quotient.mk t :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  rw [indOp, dif_pos ⟨hq, hL⟩, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem indOp_eq {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L)
    (M : Module.End ℂ P) (h : ∀ t, M (q t) = q (L t)) : indOp q L = M := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  rw [indOp_apply hq hL, h]

theorem keeps_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L * L') :=
  fun t ht => h _ (h' t ht)

theorem keeps_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L - L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem indOp_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L * L') = indOp q L * indOp q L' :=
  indOp_eq hq (keeps_mul h h') _ fun t => by
    rw [Module.End.mul_apply, indOp_apply hq h', indOp_apply hq h]; rfl

theorem indOp_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L - L') = indOp q L - indOp q L' :=
  indOp_eq hq (keeps_sub h h') _ fun t => by
    rw [LinearMap.sub_apply, indOp_apply hq h', indOp_apply hq h, LinearMap.sub_apply, map_sub]

end Ind

section Place

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp only [Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]

theorem atPl_comm {w w' : ι} (hw : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp only [Function.update_self, Function.update_of_ne hw]; first | rfl | simp [Module.End.mul_eq_comp]
  · by_cases h' : i = w'
    · subst h'; simp only [Function.update_self, Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]
    · simp only [Function.update_of_ne h, Function.update_of_ne h']

end Place

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

def fockOp (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if h : Function.Surjective q ∧ ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y)) then
    { toFun := fun Y => indOp q (atPl w (fockAct2 p₁ q₁ r s Y))
      map_add' := fun Y Z => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [LinearMap.add_apply, indOp_apply h.1 (h.2 Y), indOp_apply h.1 (h.2 Z), map_add, Main.atPl_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c Y => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [RingHom.id_apply, LinearMap.smul_apply, indOp_apply h.1 (h.2 Y), map_smul, Main.atPl_smul,
          LinearMap.smul_apply, map_smul] }
  else 0

theorem fockOp_eq {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) :
    fockOp q w Y = indOp q (atPl w (fockAct2 p₁ q₁ r s Y)) := by
  rw [fockOp, dif_pos ⟨hq, hK⟩]
  rfl

theorem fockOp_apply {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) (t : Tens F p₁ q₁ r s) :
    fockOp q w Y (q t) = q (atPl w (fockAct2 p₁ q₁ r s Y) t) := by
  rw [fockOp_eq hq hK, indOp_apply hq (hK Y)]

variable (r s) in

def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem negT_apply (Y : Mat r s) : negT r s Y = -Yᵀ := rfl

def twAct (ε : Bool) (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if ε then fockOp q w else fockOp q w ∘ₗ negT r s

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsFrames (B : Base F E) {n d : ℕ} (Y : Spc F E n) (W : Spc F E d) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) : Prop :=
  Framed B.emb (incM F Y.J) (incM F W.J) 1 Complex.I A C ∧ (∀ w, Y.θ w * A w = A w * Jm p₁ q₁) ∧
    ∀ w, W.θ w * C w = C w * Jm r s

def IsFockData (B : Base F E) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ)
    (Φ : Tens F p₁ q₁ r s →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  IsFrames B Y W A C ∧ IsFockMap B.ψ B.emb M.co A C Φ

def IsAdaptedFrame (B : Base F E) {d d₁ : ℕ} (H' : Plane E d d₁) {r s : ℕ}
    (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) (r₀ : Fin r) (s₀ : Fin s) : Prop :=
  ∀ w, (∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C w i (.inl r₀) + C w i (.inr s₀))) ∧
    (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C w i (.inl r₀) + c₂ * C w i (.inr s₀)) ∧
    ∀ a, a ≠ .inl r₀ → a ≠ .inr s₀ → ∃ z : Fin d₁ → ℂ, ∀ i, C w i a = (H'.ι.map (B.emb w).1 *ᵥ z) i

end Frames

section Laws

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

theorem atPl_sub {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' := by
  simp only [Main.atPl_eq, MultilinearMap.map_update_sub]

theorem fockOp_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y Z : Mat r s) :
    fockOp q w (Y * Z - Z * Y) = fockOp q w Y * fockOp q w Z - fockOp q w Z * fockOp q w Y := by
  rw [fockOp_eq hq hK, fockOp_eq hq hK, fockOp_eq hq hK, (GlobalTheory.FockPair.pair_lie_commute p₁ q₁ r s).2.1 Y Z,
    atPl_sub, atPl_mul, atPl_mul, indOp_sub hq (keeps_mul (hK Y) (hK Z)) (keeps_mul (hK Z) (hK Y)),
    indOp_mul hq (hK Y) (hK Z), indOp_mul hq (hK Z) (hK Y)]

theorem fockOp_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) {w w' : InfinitePlace F} (hw : w ≠ w') (Y Z : Mat r s) :
    fockOp q w Y * fockOp q w' Z = fockOp q w' Z * fockOp q w Y := by
  rw [fockOp_eq hq (hK w), fockOp_eq hq (hK w'), ← indOp_mul hq (hK w Y) (hK w' Z),
    ← indOp_mul hq (hK w' Z) (hK w Y), atPl_comm hw]

theorem negT_negT (Y : Mat r s) : negT r s (negT r s Y) = Y := by
  simp [negT_apply]

theorem negT_lie (Y Z : Mat r s) : negT r s (Y * Z - Z * Y) = negT r s Y * negT r s Z - negT r s Z * negT r s Y := by
  simp only [negT_apply, Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

theorem sameBlock_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem isKC_negT {Y : Mat r s} (hY : IsKC Y) : IsKC (negT r s Y) := fun a b hab => by
  rw [negT_apply, Matrix.neg_apply, Matrix.transpose_apply, hY b a fun h => hab (sameBlock_symm h), neg_zero]

theorem negT_Eab (a b : Ix r s) : negT r s (Eab a b) = -Eab b a := by
  rw [negT_apply, Eab, Eab, Matrix.transpose_single]

theorem twAct_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) (Y Z : Mat r s) :
    twAct ε q w (Y * Z - Z * Y) = twAct ε q w Y * twAct ε q w Z - twAct ε q w Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    rw [negT_lie, fockOp_lie hq hK]
  · simp only [twAct, if_true]
    exact fockOp_lie hq hK Y Z

theorem twAct_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) {w w' : InfinitePlace F} (hw : w ≠ w')
    (Y Z : Mat r s) : twAct ε q w Y * twAct ε q w' Z = twAct ε q w' Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    exact fockOp_comm hq hK hw _ _
  · simp only [twAct, if_true]
    exact fockOp_comm hq hK hw _ _

end Laws

end GlobalTheory.FockBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedStabX
section
noncomputable section

open GlobalTheory.WeilM GlobalTheory.KSTransfer MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

section Defs

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)

theorem map_mul_c {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    (A * B).map c = A.map c * B.map c := Matrix.map_mul (f := c.toRingHom)

def stabX {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (J : Matrix ι ι E) (X : Matrix ι (Fin r) E) :
    Subgroup (UG c J) where
  carrier := {q | ∃ a : GL (Fin r) E, ((q : GL ι E) : Matrix ι ι E) * X = X * (a : Matrix (Fin r) (Fin r) E)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by
      rw [Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro q ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    calc _ = (((q : GL ι E)⁻¹ : GL ι E) : Matrix ι ι E) * (X * (a : Matrix (Fin r) (Fin r) E)) *
          ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; rfl
      _ = _ := by rw [← ha, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

def skew (r : ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {s | sᵀ + s.map c = 0}
  zero_mem' := by ext i j; simp
  add_mem' := by
    intro s t hs ht
    ext i j
    have h1 := congrFun (congrFun hs i) j
    have h2 := congrFun (congrFun ht i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_add, Matrix.zero_apply] at *
    linear_combination h1 + h2
  neg_mem' := by
    intro s hs
    ext i j
    have h1 := congrFun (congrFun hs i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_neg, Matrix.neg_apply,
      Matrix.zero_apply] at *
    linear_combination -h1

def stdJ {m' : ℕ} (J' : Matrix (Fin m') (Fin m') E) (r : ℕ) :
    Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E :=
  Matrix.fromBlocks J' 0 0 (Matrix.fromBlocks 0 1 1 0)

def stdX (E : Type) [Field E] (m' r : ℕ) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin r) E :=
  Matrix.fromRows 0 (Matrix.fromRows 1 0)

def dualGL {r : ℕ} (a : GL (Fin r) E) : GL (Fin r) E where
  val := (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map c)ᵀ
  inv := ((a : Matrix (Fin r) (Fin r) E).map c)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.mul_inv, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.inv_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

def parMat {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (a : GL (Fin r) E) (g : GL (Fin m') E)
    (w : Matrix (Fin m') (Fin r) E) (s : Matrix (Fin r) (Fin r) E) :
    Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E :=
  Matrix.fromBlocks (g : Matrix (Fin m') (Fin m') E) (Matrix.fromCols 0 ((g : Matrix (Fin m') (Fin m') E) * w))
    (Matrix.fromRows (-((a : Matrix (Fin r) (Fin r) E) * ((w.map c)ᵀ * J'ᵀ))) 0)
    (Matrix.fromBlocks (a : Matrix (Fin r) (Fin r) E)
      ((a : Matrix (Fin r) (Fin r) E) * (s - (2 : E)⁻¹ • ((w.map c)ᵀ * J'ᵀ * w))) 0
      ((dualGL c a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))

def omega {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (w w' : Matrix (Fin m') (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  (2 : E)⁻¹ • ((w'.map c)ᵀ * J'ᵀ * w - (w.map c)ᵀ * J'ᵀ * w')

end Defs

section Top

variable {k E : Type} [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Top

section Mod

variable {k E : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Field E] [Algebra k E]
  {c : E →ₐ[k] E} {r : ℕ}

end Mod

section Steps

def IsWeight {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (Q : Subgroup G) (ν : Measure Q)
    (φ : G → ℝ) : Prop :=
  Measurable φ ∧ (∀ g, 0 ≤ φ g) ∧ (∃ (K : Set G) (B : ℝ), IsCompact K ∧ ∀ g, φ g ≤ B ∧ (φ g ≠ 0 → g ∈ K)) ∧
    ∀ g, ∫⁻ q : Q, ENNReal.ofReal (φ ((q : G)⁻¹ * g)) ∂ν = 1

def WeightExists : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (Q : Subgroup G), IsClosed (Q : Set G) →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ Q, ∃ x ∈ C, g = q * x) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Q) [ν.IsHaarMeasure],
      ∃ φ : G → ℝ, IsWeight Q ν φ ∧ ∀ U ∈ nhds (1 : G), 0 < ∫ g in U, φ g ∂μ

def WeightIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (Q : Subgroup G) [LocallyCompactSpace Q]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Q) [ν.IsHaarMeasure] (φ φ' : G → ℝ), IsWeight Q ν φ → IsWeight Q ν φ' →
    ∀ F : G → ℂ, Continuous F → (∀ (q : Q) (g : G), F (q * g) = ((modularCharacterFun q : ℝ) : ℂ) * F g) →
      ∫ g, (φ g : ℂ) * F g ∂μ = ∫ g, (φ' g : ℂ) * F g ∂μ

def AvgAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] (Q : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → (∀ g : G, modularCharacterFun g = 1) →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ Q, ∃ x ∈ C, g = q * x) →
    ∃ Av : (G → ℂ) →ₗ[ℂ] ℂ,
      (∀ U : Subgroup G, IsOpen (U : Set G) → ∃ (s : Finset G) (w : G → ℂ),
        ∀ F : G → ℂ, (∀ g, ∀ u ∈ U, F (g * u) = F g) → Av F = ∑ g ∈ s, w g * F g) ∧
      (∀ F : G → ℂ, (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ (q : Q) (g : G), F (q * g) = ((modularCharacterFun q : ℝ) : ℂ) * F g) →
        ∀ g₀, Av (fun g => F (g * g₀)) = Av F) ∧
      (∀ F : G → ℂ, (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → F 1 ≠ 0 → Av F ≠ 0)

def ChartMod : Prop :=
  ∀ (Q M A B : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q]
    [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [T2Space B] [MeasurableSpace B] [BorelSpace B]
    (Φ : M × A × B ≃ₜ Q) (L₁ : M → A ≃ₜ+ A) (L₂ : M → B ≃ₜ+ B) (ω : A → A → B), (∀ x : M, modularCharacterFun x = 1) →
    (∀ x a b x' a' b', Φ (x, a, b) * Φ (x', a', b') = Φ (x * x', L₁ x' a + a', L₂ x' b + b' + ω (L₁ x' a) a')) →
    ∀ x a b, modularCharacterFun (Φ (x, a, b)) * (addEquivAddHaarChar (L₁ x) * addEquivAddHaarChar (L₂ x)) = 1

def UnimodU : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm c J → ∀ [LocallyCompactSpace (UG c J)] (g : UG c J),
    modularCharacterFun g = 1

def UnimodM : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (r n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm c J →
    ∀ [LocallyCompactSpace (GL (Fin r) E × UG c J)] (x : GL (Fin r) E × UG c J), modularCharacterFun x = 1

def AbsExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
    ∃ v : E →*₀ ℝ≥0, IsCompact {y : E | v y ≤ 1}

def FrameCpt : Prop :=
  ∀ (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] (v : E →*₀ ℝ≥0),
    IsCompact {y : E | v y ≤ 1} → ∀ m r : ℕ, ∃ S : Set (Matrix (Fin m) (Fin r) E), IsCompact S ∧
      (∀ Y ∈ S, ∀ u, Y *ᵥ u = 0 → u = 0) ∧ ∀ Y : Matrix (Fin m) (Fin r) E, (∀ u, Y *ᵥ u = 0 → u = 0) →
        ∃ Y₀ ∈ S, ∃ a : GL (Fin r) E, Y = Y₀ * (a : Matrix (Fin r) (Fin r) E)

def Cocpt : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ (m r : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm c J → ∀ X : Matrix (Fin m) (Fin r) E, Xᵀ * J * X.map c = 0 →
    (∀ u, X *ᵥ u = 0 → u = 0) → ∃ C : Set (UG c J), IsCompact C ∧ ∀ g, ∃ q ∈ stabX c J X, ∃ x ∈ C, g = q * x

def JacMat : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (p q : ℕ) [LocallyCompactSpace (Matrix (Fin p) (Fin q) E)]
    [MeasurableSpace (Matrix (Fin p) (Fin q) E)] [BorelSpace (Matrix (Fin p) (Fin q) E)]
    (g : GL (Fin p) E) (a : GL (Fin q) E) (L : Matrix (Fin p) (Fin q) E ≃ₜ+ Matrix (Fin p) (Fin q) E),
    (∀ u, L u = (g : Matrix (Fin p) (Fin p) E) * u * (a : Matrix (Fin q) (Fin q) E)) →
      (addEquivAddHaarChar L : ℝ) = detMod k g ^ q * detMod k a ^ p

def JacSkew : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (r : ℕ) [LocallyCompactSpace (skew c r)] [MeasurableSpace (skew c r)] [BorelSpace (skew c r)]
    (a : GL (Fin r) E) (L : skew c r ≃ₜ+ skew c r),
    (∀ s, (L s : Matrix (Fin r) (Fin r) E) = ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (s : Matrix (Fin r) (Fin r) E) *
      ((dualGL c a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) → (addEquivAddHaarChar L : ℝ) * detMod k a ^ r = 1

def ParUnit : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' → ∀ (a : GL (Fin r) E) (g : UG c J')
    (w : Matrix (Fin m') (Fin r) E) (s : Matrix (Fin r) (Fin r) E), s ∈ skew c r →
      (parMat c J' a g w s)ᵀ * stdJ J' r * (parMat c J' a g w s).map c = stdJ J' r

def ParLaw : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E) (a a' : GL (Fin r) E) (g g' : UG c J')
    (w w' w₁ : Matrix (Fin m') (Fin r) E) (s s' s₁ : Matrix (Fin r) (Fin r) E),
    w₁ = (((g' : GL (Fin m') E)⁻¹ : GL (Fin m') E) : Matrix (Fin m') (Fin m') E) * w *
      ((dualGL c a' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) →
    s₁ = ((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * s * ((dualGL c a' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) →
      parMat c J' a g w s * parMat c J' a' g' w' s' =
        parMat c J' (a * a') ((g * g' : UG c J') : GL (Fin m') E) (w₁ + w') (s₁ + s' + omega c J' w₁ w')

def ParDec : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' → ∀ (q : UG c (stdJ J' r)) (a : GL (Fin r) E),
    ((q : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
      stdX E m' r * (a : Matrix (Fin r) (Fin r) E) →
    ∃ (g : UG c J') (w : Matrix (Fin m') (Fin r) E), ∃ s ∈ skew c r,
      ((q : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) =
        parMat c J' a g w s

def ParChart : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] (c : E →ₐ[k] E),
    Continuous c → (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' →
    ∃ (Φ : (GL (Fin r) E × UG c J') × Matrix (Fin m') (Fin r) E × skew c r ≃ₜ stabX c (stdJ J' r) (stdX E m' r))
      (L₁ : GL (Fin r) E × UG c J' → Matrix (Fin m') (Fin r) E ≃ₜ+ Matrix (Fin m') (Fin r) E)
      (L₂ : GL (Fin r) E × UG c J' → skew c r ≃ₜ+ skew c r)
      (ω : Matrix (Fin m') (Fin r) E → Matrix (Fin m') (Fin r) E → skew c r),
      (∀ x w, L₁ x w = (((x.2 : GL (Fin m') E)⁻¹ : GL (Fin m') E) : Matrix (Fin m') (Fin m') E) * w *
        ((dualGL c x.1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ∧
      (∀ x s, (L₂ x s : Matrix (Fin r) (Fin r) E) = ((x.1⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
        (s : Matrix (Fin r) (Fin r) E) * ((dualGL c x.1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ∧
      (∀ x w s x' w' s', Φ (x, w, s) * Φ (x', w', s') = Φ (x * x', L₁ x' w + w', L₂ x' s + s' + ω (L₁ x' w) w')) ∧
      ∀ x w s, (((Φ (x, w, s) : UG c (stdJ J' r)) : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) :
        Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
          stdX E m' r * (x.1 : Matrix (Fin r) (Fin r) E)

def StabTransport : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] (c : E →ₐ[k] E)
    (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → Pᵀ * JA * P.map c = stdJ J' r →
    (∃ p : Matrix (Fin r) (Fin m) E, p * colX P = 1) ∧ (colX P)ᵀ * JA * (colX P).map c = 0 ∧
    ∃ e : stabX c (stdJ J' r) (stdX E m' r) ≃ₜ* stabX c JA (colX P), ∀ (q : stabX c (stdJ J' r) (stdX E m' r))
      (a : GL (Fin r) E), (((q : UG c (stdJ J' r)) : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) :
        Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
          stdX E m' r * (a : Matrix (Fin r) (Fin r) E) →
      (((e q : UG c JA) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * colX P = colX P * (a : Matrix (Fin r) (Fin r) E)

end Steps

section Law

end Law

end GlobalTheory.ParAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.schA_periodic_finite_cosets | exact GlobalTheory.WeilCont.schA_periodic_finite_cosets | (intros; apply GlobalTheory.WeilCont.schA_periodic_finite_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartzStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  first | exact @GlobalTheory.PolDense.pol_dense | exact GlobalTheory.PolDense.pol_dense | (intros; apply GlobalTheory.PolDense.pol_dense <;> assumption)
end

