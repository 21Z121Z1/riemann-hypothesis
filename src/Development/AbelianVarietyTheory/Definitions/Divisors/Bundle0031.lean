import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.CircleAsphGNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTvalNeZero
section
noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_locLat_const (g : Matrix ι ι K) (x : ι → K) :
    x ∈ locLat (fun _ : HeightOneSpectrum (𝓞 K) => g) ↔ ∀ i, (g *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range :=
  ⟨fun h i => HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun w => h w i,
   fun h w i => by obtain ⟨a, ha⟩ := h i; rw [← ha]; exact w.valuation_le_one a⟩

theorem finite_not_le (a : K) : {w : HeightOneSpectrum (𝓞 K) | ¬ w.valuation K a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · simp [ha]
  refine (GlobalTheory.FlatLine.finite_vAdd ha).subset fun w hw h0 => hw ?_
  have h1 : vAdd w a = 0 := Int.cast_eq_zero.1 h0
  have h2 : w.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [vAdd, neg_eq_zero] at h1
  rw [← WithZero.exp_log h2, h1]; simp

theorem finite_not_intAt (g : Matrix ι ι K) : {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w g}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => finite_not_le (g p.1 p.2)).subset fun w hw => ?_
  simp only [IntAt, Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨i, j, h⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), h⟩

theorem isAdelic_const {g : Matrix ι ι K} (hg : g.det ≠ 0) : IsAdelic (fun _ : HeightOneSpectrum (𝓞 K) => g) :=
  ⟨fun _ => hg, ((finite_not_intAt g).union (finite_not_intAt g⁻¹)).subset fun w hw => by
    simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hw ⊢; exact hw⟩

open Classical in

theorem isAdelic_single (v : HeightOneSpectrum (𝓞 K)) {g : Matrix ι ι K} (hg : g.det ≠ 0) :
    IsAdelic (fun w : HeightOneSpectrum (𝓞 K) => if w = v then g else 1) := by
  refine ⟨fun w => by by_cases h : w = v <;> simp [h, hg], (Set.finite_singleton v).subset fun w hw => ?_⟩
  by_contra h
  have h' : w ≠ v := h
  have h1 : IntAt w (1 : Matrix ι ι K) := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  exact hw (by simp [h', h1])

theorem not_isAdelic_zero [Nonempty ι] (v : HeightOneSpectrum (𝓞 K)) :
    ¬ IsAdelic (fun _ : HeightOneSpectrum (𝓞 K) => (0 : Matrix ι ι K)) := fun h => h.1 v (by simp)

theorem detDeg_const {g : Matrix ι ι K} (hg : g.det ≠ 0) :
    detDeg (fun _ : HeightOneSpectrum (𝓞 K) => g) (fun σ => g.map σ) = 0 := by
  have := GlobalTheory.FlatLine.lineDeg_num hg
  simpa only [detDeg, RingHom.map_det, RingHom.mapMatrix_apply] using this

theorem matNorm_map (g : Matrix ι ι K) (σ : K →+* ℂ) (x : ι → K) :
    matNorm (fun σ => g.map σ) σ x = matNorm (fun _ => 1) σ (g *ᵥ x) := by
  simp only [matNorm, Matrix.one_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec]; rfl

theorem detDeg_nat {n : ℕ} (hn : n ≠ 0) :
    detDeg (fun _ : HeightOneSpectrum (𝓞 K) => !![(n : K)]) (fun _ => 1) = Real.log n := by
  simp [detDeg, GlobalTheory.FlatLine.lineDeg, GlobalTheory.FlatLine.sum_vAdd_nat hn]

theorem inv_mem {n : ℕ} (hn : n ≠ 0) :
    ![(n : K)⁻¹] ∈ locLat (fun _ : HeightOneSpectrum (𝓞 K) => !![(n : K)]) := fun w i => by
  have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  fin_cases i
  simp [Matrix.mulVec, dotProduct, this]

end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

theorem evalAt_eq_sum (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (y : Matrix (Fin n) (Fin n) K) (f : nabla la K) :
    evalAt y f.1 = ∑ i, (basis la K).repr f i * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h := congrArg (fun f : nabla la K => evalAt y f.1) ((basis la K).sum_repr f)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul, coe_basis] at h
  exact h.symm

theorem evalAt_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g y : Matrix (Fin n) (Fin n) K) (j : Idx la) :
    evalAt (g * y) (map (Int.castRingHom K) (intVec la j)) =
      ∑ i, rhoMat la g i j * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h1 := evalAt_rho y gᵀ (basis la K j)
  rw [Matrix.transpose_transpose, coe_basis] at h1
  rw [← h1, evalAt_eq_sum]
  simp only [rhoMat, LinearMap.toMatrix_apply]

theorem tval_mul (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (x : TIdx la → K)
    (g y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    tval la x (fun t => g t * y t) = tval la (fibA la 1 g *ᵥ x) y := by
  simp only [tval, evalAt_mul, fibA, one_smul, Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]; ring

theorem kron_mul {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron fun t => M t * M' t := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

theorem onMat_mulVec (la : Fin n → ℕ) (f : nabla la ℂ) :
    onMat la *ᵥ (basis la ℂ).repr f = (onBasis la).repr (toSpace la f) := by
  funext i
  have h := congrArg (fun f : nabla la ℂ => (onBasis la).repr (toSpace la f) i) ((basis la ℂ).sum_repr f)
  simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  simp only [onMat, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]

theorem sum_sq_onMat (la : Fin n → ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (f : nabla la ℂ) :
    ∑ i, ‖((onMat la * rhoMat la X) *ᵥ (basis la ℂ).repr f) i‖ ^ 2 = normSq la (Formalism.GradedWeylDivisibility.rowAct ℂ X f.1) := by
  have h : rhoMat la X *ᵥ (basis la ℂ).repr f = (basis la ℂ).repr (rho la ℂ Xᵀ f) :=
    LinearMap.toMatrix_mulVec_repr _ _ _ _
  rw [← Matrix.mulVec_mulVec, h, onMat_mulVec, ← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map,
    norm_toSpace_sq, coe_rho, Matrix.transpose_transpose]

theorem nonempty_tIdx (la : ∀ t, Fin (N t) → ℕ) (h : ∀ t, Antitone (la t)) : Nonempty (TIdx la) :=
  ⟨fun t => (Fintype.card_pos_iff.1 (dim_eq_card (la t) ▸ dim_pos (h t))).some⟩

theorem exists_tval_ne_zero (la : Fin n → ℕ) (h : Antitone la) :
    ∃ x : TIdx (fun _ : Unit => la) → ℚ, tval (fun _ : Unit => la) x (fun _ => 1) = 1 := by
  refine ⟨fun I => (basis la ℚ).repr ⟨extremal la ℚ, extremal_mem h⟩ (I ()), ?_⟩
  have h2 := evalAt_eq_sum la 1 (⟨extremal la ℚ, extremal_mem h⟩ : nabla la ℚ)
  rw [evalAt_one_extremal] at h2
  rw [h2, tval, ← (Equiv.funUnique Unit (Idx la)).symm.sum_comp]
  simp

theorem fibA_mul (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (a b : K)
    (g h : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) : fibA la a g * fibA la b h = fibA la (a * b) fun t => h t * g t := by
  simp only [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, rhoMat_mul, smul_smul, mul_comm]

theorem fibY_eq (la : ∀ t, Fin (N t) → ℕ) (s : ℝ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    fibY la s X = fibY la s (fun _ => 1) * fibA la 1 X := by
  simp only [fibY, fibA, rhoMat_one, Matrix.mul_one, one_smul, Matrix.smul_mul, kron_mul]

theorem fibA_two : fibA (fun _ : Unit => ![1, 0]) (1 : ℚ) (fun _ => (2 : ℚ) • 1) = (2 : ℚ) • 1 := by
  ext I J
  simp only [fibA, kron, rhoMat_scalar, one_smul, Matrix.of_apply, Finset.univ_unique, Finset.prod_singleton,
    Matrix.smul_apply, Matrix.one_apply, size, Fin.sum_univ_two]
  by_cases h : I = J
  · simp [h]
  · have : I default ≠ J default := fun h' => h (funext fun _ => h')
    simp [h, this]

end Tensor

end GlobalTheory.DefPt.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
section
noncomputable section

namespace GlobalTheory.KS

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

abbrev pow (A : Over S) (m : ℕ) : Over S := ∏ᶜ fun _ : Fin m => A

abbrev pr (A : Over S) {m : ℕ} (i : Fin m) : pow A m ⟶ A := Pi.π (fun _ : Fin m => A) i

def matEnd {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : pow A m ⟶ pow A m :=
  Pi.lift fun i => (List.ofFn fun j => pr A j ≫ act.act (M i j)).prod

def powMap {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (h : φ ≫ A.hom = A'.hom ≫ f)
    (m : ℕ) : (pow A' m).left ⟶ (pow A m).left :=
  (Pi.lift (fun i => Over.homMk ((pr A' i).left ≫ φ) (by
    rw [Category.assoc, h, ← Category.assoc, Over.w]; rfl)) : Over.mk ((pow A' m).hom ≫ f) ⟶ pow A m).left

variable {B B' : Scheme.{0}}

abbrev ksBC (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : Scheme.{0} := pullback ((pow A m).hom ≫ p) b

def matBC {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (M : Matrix (Fin m) (Fin m) O) :
    ksBC A m p b ⟶ ksBC A m p b :=
  pullback.map _ _ _ _ (matEnd act M).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp)

variable (l : ℕ) [Fact l.Prime] (E : Type) [CommRing E] [Algebra ℚ_[l] E]

abbrev HE (Y : Scheme.{0}) (n : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n 0

def pullE {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : HE l E Y' n →ₗ[E] HE l E Y n :=
  (pullHQ l (sch.map u) n 0).baseChange E

variable {E}

def op {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n : ℤ) : Module.End E (HE l E (ksBC A m p b) n) :=
  ε.sum fun M c => c • pullE l E (matBC act p b M) n

def Hxi {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (k : ℕ) (i : ℤ) : Submodule E (HE l E (ksBC A m p b) (i + k)) :=
  LinearMap.range (op l act p b ε (i + k))

def galE (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) : Module.End E (HE l E (GlobalTheory.Et.geom Ω q) n) :=
  pullE l E (GlobalTheory.Et.galMap Ω q σ) n

variable (E) in

abbrev HEt (Y : Scheme.{0}) (n t : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n t

variable (E) in

def pullEt {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n t : ℤ) : HEt l E Y' n t →ₗ[E] HEt l E Y n t :=
  (pullHQ l (sch.map u) n t).baseChange E

def opT {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n t : ℤ) : Module.End E (HEt l E (ksBC A m p b) n t) :=
  ε.sum fun M c => c • pullEt l E (matBC act p b M) n t

def HxiT {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (k : ℕ) (t i : ℤ) : Submodule E (HEt l E (ksBC A m p b) (i + k) t) :=
  LinearMap.range (opT l act p b ε (i + k) t)

def galEt (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (n t : ℤ) (σ : Ω ≃ₐ[k] Ω) : Module.End E (HEt l E (GlobalTheory.Et.geom Ω q) n t) :=
  pullEt l E (GlobalTheory.Et.galMap Ω q σ) n t

variable (E) in
theorem pullEt_zero {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : pullEt l E u n 0 = pullE l E u n := rfl

theorem opT_zero {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (n : ℤ) : opT l act p b ε n 0 = op l act p b ε n := rfl

theorem HxiT_zero {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) (i : ℤ) : HxiT l act p b ε k 0 i = Hxi l act p b ε k i := rfl

theorem galEt_zero (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    galEt l E Ω q n 0 σ = galE l E Ω q n σ := rfl

example (Y : Scheme.{0}) (n : ℤ) : HEt l E Y n 0 = HE l E Y n := rfl

@[simp] theorem opT_zero_comb {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (n t : ℤ) :
    opT l act p b (0 : Matrix (Fin m) (Fin m) O →₀ E) n t = 0 := by
  simp [opT]

theorem HxiT_zero_comb {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (k : ℕ) (t i : ℤ) :
    HxiT l act p b (0 : Matrix (Fin m) (Fin m) O →₀ E) k t i = ⊥ := by
  rw [HxiT, opT_zero_comb, LinearMap.range_zero]

theorem opT_add {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε ε' : Matrix (Fin m) (Fin m) O →₀ E) (n t : ℤ) : opT l act p b (ε + ε') n t = opT l act p b ε n t + opT l act p b ε' n t := by
  unfold opT
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

abbrev latRep {p : ℕ} [Fact p.Prime] (D : Datum p) : D.O →+* Module.End ℤ D.La := Module.toModuleEnd ℤ D.La

example {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (A : Over S) (m : ℕ) (p : S ⟶ Spec (CommRingCat.of k)) :
    ksBC A m p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = GlobalTheory.Et.geom Ω ((pow A m).hom ≫ p) := rfl

def ArtinQE (E : Type) [Field E] [Algebra ℚ_[l] E] : Prop :=
  ∃ e : ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p] (n : ℕ),
      HE l E X n ≃ₗ[E] SH E (GlobalTheory.CxPts p (RingHom.id ℂ)) n,
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
      (q : Y ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
      (u : X ⟶ Y) (g : C(GlobalTheory.CxPts p (RingHom.id ℂ), GlobalTheory.CxPts q (RingHom.id ℂ))), u ≫ q = p → (∀ x, (g x).1 = x.1 ≫ u) →
      ∀ (n : ℕ) (y : HE l E Y n), e X p n (pullE l E u n y) = shMap E g n (e Y q n y)

def trivMap (E : Type) [Field E] {G G' : Type} [Group G] [Group G'] (α : G' →* G) :
    Rep.res α (Rep.trivial E G E) ⟶ Rep.trivial E G' E :=
  Rep.ofHom { toLinearMap := LinearMap.id, isIntertwining' := fun _ => rfl }

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.LBObs

section Frames

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

def IsBas (V : C → X.Opens) : Prop :=
  (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C, x ∈ V t ∧ V t ≤ U) ∧
    ∀ (t₁ t₂ : C) (x : X) (U : X.Opens), x ∈ U → x ∈ V t₁ → x ∈ V t₂ →
      ∃ t₃ : C, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ V t₃ ∧ V t₃ ≤ U

def IsGenOn (L : LB X) (W : X.Opens) (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) : Prop :=
  ∀ m m' : L.ι, res (inf_le_left : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m) (τ m) =
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m') (L.g m m') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m') (τ m')

def IsFrame (L : LB X) (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∃ τ : ∀ (T : C) (m : L.ι), Γ(X, V T ⊓ L.U m)ˣ, (∀ T, IsGenOn L (V T) (τ T)) ∧
    ∀ (T T' : C) (a : T ⟶ T') (m : L.ι), res (inf_le_inf_right (L.U m) (hV a)) (τ T m) =
      res (inf_le_left : V T' ⊓ L.U m ≤ V T') (u T T' a) * τ T' m

def IsCoc (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''), u T T'' (a ≫ b) = res (hV b) (u T T' a) * u T' T'' b

abbrev opOf (G : C ⥤ AffOp X) (T : C) : X.Opens := (G.obj T).unop.1

theorem opOf_le (G : C ⥤ AffOp X) ⦃T T' : C⦄ (a : T ⟶ T') : opOf G T' ≤ opOf G T := leOfHom (G.map a).unop

theorem isCoc_one (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) : IsCoc V hV fun _ _ _ ↦ 1 :=
  fun _ _ _ _ _ ↦ by simp

theorem isBas_opens : IsBas (C := (X.Opens)ᵒᵖ) fun U ↦ U.unop :=
  ⟨fun _ U hx ↦ ⟨Opposite.op U, hx, le_rfl⟩, fun t₁ t₂ _ U hx h₁ h₂ ↦
    ⟨Opposite.op (t₁.unop ⊓ t₂.unop ⊓ U), ⟨(homOfLE (inf_le_left.trans inf_le_left)).op⟩,
      ⟨(homOfLE (inf_le_left.trans inf_le_right)).op⟩, ⟨⟨h₁, h₂⟩, hx⟩, inf_le_right⟩⟩

end Frames

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

def UCoc (F : C ⥤ CommAlgCat.{0} R₀) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''),
    (u T T'' (a ≫ b) : F.obj T'') = mp F b (u T T' a : F.obj T') * (u T' T'' b : F.obj T'')

def IsObU (L : Pre I π F) (α : Aug I π R₁) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ)
    (c : CatCoh.H2 (ext R₁ F)) : Prop :=
  ∃ (v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T) (z : Z2 (ext R₁ F)),
    (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ (∀ T, α.IsSig (L.p T) (σ T)) ∧ c = H2.mk _ z ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), α.KerQ (B₀ := F.obj T'') (z.1 T T' T'' a b) ∧
        L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z.1 T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'')

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}

def ObAt (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (G : C ⥤ AffOp X₀) (d : CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))) : Prop :=
  ∃ u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X₀, opOf G T')ˣ,
    IsFrame L (opOf G) (opOf_le G) u ∧ IsObU ((ofSys S).restrict G) α u d

def IsObL (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (c : CatCoh.H2 (ext R₁ (OAff s₀))) : Prop :=
  ∃ (C' : Type) (_ : Category.{0} C') (_ : Quiver.IsThin C') (G : C' ⥤ AffOp X₀), IsBas (opOf G) ∧
    ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)

theorem isObU_one (L : Pre I π F) (α : Aug I π R₁) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T)
    (hσ : ∀ T, α.IsSig (L.p T) (σ T)) : IsObU L α (fun _ _ _ ↦ 1) 0 :=
  ⟨fun _ _ _ ↦ 1, σ, 0, fun _ _ _ ↦ by simp, hσ, (map_zero _).symm, fun T T' T'' a b ↦
    ⟨map_zero _, by
      have : (0 : Z2 (ext R₁ F)).1 T T' T'' a b = 0 := rfl
      rw [this, map_zero]; simp⟩⟩

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

def IsGal {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} (π : W ⟶ Z) (hπ : π ≫ s = sW) (G : Type) [Group G]
    (act : G → (W ⟶ W)) : Prop :=
  GlobalTheory.ZM.IsGaloisCover G (fun g => act g⁻¹) π

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

theorem mk' (hG : Finite G) (hfin : IsFinite π) (het : Etale π) (hon : Surjective π) (hinv : ∀ g, act g ≫ π = π)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) (hone : act 1 = 𝟙 W)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W), a ≫ π = b ≫ π → ∃! g : G, b = a ≫ act g) :
    IsGal π hπ G act where
  finite := hG
  one := by simp [hone]
  mul a c := by simp only [mul_inv_rev]; exact hmul c⁻¹ a⁻¹
  inv a := hinv a⁻¹
  fin := hfin
  etale := het
  onto := hon
  fibre K _ _ y y' e := by
    obtain ⟨g, hg, hu⟩ := hfib K y y' e
    refine ⟨g⁻¹, by simp [hg], fun a ha => ?_⟩
    have := hu a⁻¹ (by simpa using ha.symm)
    simp [← this]

theorem finite (h : IsGal π hπ G act) : Finite G := GlobalTheory.ZM.IsGaloisCover.finite h
theorem isFinite (h : IsGal π hπ G act) : IsFinite π := GlobalTheory.ZM.IsGaloisCover.fin h
theorem etale (h : IsGal π hπ G act) : Etale π := GlobalTheory.ZM.IsGaloisCover.etale h
theorem surjective (h : IsGal π hπ G act) : Surjective π := GlobalTheory.ZM.IsGaloisCover.onto h

theorem act_comp (h : IsGal π hπ G act) (g : G) : act g ≫ π = π := by
  simpa using GlobalTheory.ZM.IsGaloisCover.inv h g⁻¹

theorem act_mul (h : IsGal π hπ G act) (g g' : G) : act (g * g') = act g' ≫ act g := by
  simpa using GlobalTheory.ZM.IsGaloisCover.mul h g'⁻¹ g⁻¹

theorem act_one (h : IsGal π hπ G act) : act 1 = 𝟙 W := by
  simpa using GlobalTheory.ZM.IsGaloisCover.one h

theorem fibre (h : IsGal π hπ G act) (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W) :
    a ≫ π = b ≫ π ↔ ∃! g : G, b = a ≫ act g := by
  constructor
  · intro e
    obtain ⟨g, hg, hu⟩ := GlobalTheory.ZM.IsGaloisCover.fibre h K a b e
    refine ⟨g⁻¹, hg.symm, fun g' hg' => ?_⟩
    have := hu g'⁻¹ (by simpa using hg'.symm)
    simp [← this]
  · rintro ⟨g, hg, -⟩
    rw [hg, Category.assoc, h.act_comp]

theorem fibre_cx (h : IsGal π hπ G act) (a b : CxPts sW (RingHom.id ℂ)) :
    a.1 ≫ π = b.1 ≫ π ↔ ∃! g : G, b.1 = a.1 ≫ act g :=
  h.fibre ℂ a.1 b.1

end IsGal

example : IsGal (Z := Sp ℂ) (W := Sp ℂ) (s := 𝟙 _) (sW := 𝟙 _) (𝟙 _) (by simp) Unit (fun _ => 𝟙 _) :=
  IsGal.mk' inferInstance inferInstance inferInstance inferInstance (fun _ => by simp) (fun _ _ => by simp) rfl
    (fun _ _ _ a b e => ⟨(), by simpa using e.symm, fun _ _ => rfl⟩)

example (G : Type) [Group G] : ¬ IsGal (Z := Sp ℂ) (W := (∅ : Scheme.{0})) (s := 𝟙 _) (sW := Scheme.emptyTo _)
    (Scheme.emptyTo _) (by simp) G (fun _ => 𝟙 _) := by
  intro h
  have := h.surjective
  obtain ⟨x, -⟩ := (Scheme.emptyTo (Sp ℂ)).surjective (IsLocalRing.closedPoint ℂ)
  exact isEmptyElim x

example : ¬ IsGal (Z := Sp ℂ) (W := Sp ℂ) (s := 𝟙 _) (sW := 𝟙 _) (𝟙 _) (by simp) ℤˣ (fun _ => 𝟙 _) := by
  intro h
  obtain ⟨g, -, hu⟩ := (h.fibre ℂ (𝟙 _) (𝟙 _)).1 rfl
  have := (hu 1 (by simp)).trans (hu (-1) (by simp)).symm
  exact absurd this (by decide)

end GlobalTheory.W1
end
end

