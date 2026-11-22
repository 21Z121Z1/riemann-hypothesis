import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import GroundTheory.Brauer.Splitting
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeMapFApply
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeEl

variable {T : Type 1} [Category.{0} T] {C D : T ⥤ AbCx} (φ : C ⟶ D)

def coneD (U : T) (n : ℤ) :
    AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n) ⟶
      AddCommGrpCat.of ((C.obj U).X (n + 1 + 1) × (D.obj U).X (n + 1)) :=
  AddCommGrpCat.ofHom
    { toFun := fun x => (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2)
      map_zero' := by simp
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, map_add, neg_add] <;> abel }

lemma coneD_apply (U : T) (n : ℤ) (x : (C.obj U).X (n + 1) × (D.obj U).X n) :
    coneD φ U n x = (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2) := rfl

lemma dd_apply (K : AbCx) (i j k : ℤ) (x : K.X i) : K.d j k (K.d i j x) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]; rfl

lemma comm_apply {K L : AbCx} (f : K ⟶ L) (i j : ℤ) (x : K.X i) : f.f j (K.d i j x) = L.d i j (f.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm]

lemma coneD_sq (U : T) (n : ℤ) : coneD φ U n ≫ coneD φ U (n + 1) = 0 := by
  refine AddCommGrpCat.ext fun x => ?_
  change coneD φ U (n + 1) (coneD φ U n x) = 0
  rw [coneD_apply, coneD_apply]
  refine Prod.ext ?_ ?_
  · simp [dd_apply]
  · simp [dd_apply, comm_apply]

def coneObj (U : T) : AbCx :=
  CochainComplex.of (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) (coneD_sq φ U)

lemma nat_apply {U V : T} (g : U ⟶ V) (n : ℤ) (x : (C.obj U).X n) :
    (D.map g).f n ((φ.app U).f n x) = (φ.app V).f n ((C.map g).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

def coneMap {U V : T} (g : U ⟶ V) : coneObj φ U ⟶ coneObj φ V :=
  CochainComplex.ofHom (X := coneObj φ U) (Y := coneObj φ V)
    (fun n => AddCommGrpCat.ofHom (AddMonoidHom.prodMap ((C.map g).f (n + 1)).hom ((D.map g).f n).hom))
    (fun n => by
      refine AddCommGrpCat.ext fun x => ?_
      simp only [coneObj, CochainComplex.of_d]
      change coneD φ V n (((C.map g).f (n + 1)) x.1, ((D.map g).f n) x.2) =
        (((C.map g).f (n + 1 + 1)) (coneD φ U n x).1, ((D.map g).f (n + 1)) (coneD φ U n x).2)
      rw [coneD_apply]
      erw [coneD_apply]
      refine Prod.ext ?_ ?_
      · simp [comm_apply]
      · simp [comm_apply, nat_apply])

@[simp] lemma coneMap_f_apply {U V : T} (g : U ⟶ V) (n : ℤ) (x : (coneObj φ U).X n) :
    (coneMap φ g).f n x = ((C.map g).f (n + 1) x.1, (D.map g).f n x.2) := rfl

def cone : T ⥤ AbCx where
  obj := coneObj φ
  map := coneMap φ
  map_id U := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (𝟙 U)).f (n + 1) x.1 = x.1
      rw [CategoryTheory.Functor.map_id]; rfl
    · change (D.map (𝟙 U)).f n x.2 = x.2
      rw [CategoryTheory.Functor.map_id]; rfl
  map_comp f g := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (f ≫ g)).f (n + 1) x.1 = (C.map g).f (n + 1) ((C.map f).f (n + 1) x.1)
      rw [CategoryTheory.Functor.map_comp]; rfl
    · change (D.map (f ≫ g)).f n x.2 = (D.map g).f n ((D.map f).f n x.2)
      rw [CategoryTheory.Functor.map_comp]; rfl

def coneFst (n : ℤ) : term (cone φ) n ⟶ term C (n + 1) where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality U V g := rfl

def coneSnd (n : ℤ) : term (cone φ) n ⟶ term D n where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  naturality U V g := rfl

end GlobalTheory.EtC.ConeEl

open GlobalTheory.EtC.ConeEl in

theorem GlobalTheory.EtC.coneEl_exists : ∀ (T : Type 1) [Category.{0} T] (C D : T ⥤ AbCx) (φ : C ⟶ D), ∃ (K : T ⥤ AbCx) (p : ∀ n : ℤ, term K n ⟶ term C (n + 1)) (q : ∀ n : ℤ, term K n ⟶ term D n), (∀ n U, Function.Bijective (fun x : (K.obj U).X n => ((p n).app U x, (q n).app U x))) ∧ ∀ n U (x : (K.obj U).X n), (p (n + 1)).app U ((K.obj U).d n (n + 1) x) = - (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) ∧ (q (n + 1)).app U ((K.obj U).d n (n + 1) x) = (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) := by
  intro T _ C D φ
  refine ⟨cone φ, coneFst φ, coneSnd φ, fun n U => ?_, fun n U x => ?_⟩
  · refine ⟨fun x y h => ?_, fun y => ⟨(y.1, y.2), rfl⟩⟩
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have hd : (cone φ |>.obj U).d n (n + 1) = coneD φ U n := CochainComplex.of_d (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) n
    constructor
    · change ((cone φ |>.obj U).d n (n + 1) x).1 = _
      rw [hd]; rfl
    · change ((cone φ |>.obj U).d n (n + 1) x).2 = _
      rw [hd]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLe
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]

theorem opNorm_one_le_of_entry (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring

theorem inv_entry_le (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det ∧ ∀ j k, |Y⁻¹ j k| ≤ 1 / c := by
  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hY x
    rw [hx0, dotProduct_zero] at h1
    have h2 : x ⬝ᵥ x ≤ 0 := by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]
    apply hx
    funext i
    have h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  refine ⟨hdet, fun j k => ?_⟩
  set u := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have hYu : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hentry : Y⁻¹ j k = u j := by
    rw [hu, mulVec_single_one]; rfl
  set N := u ⬝ᵥ u with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hcomp : ∀ i, u i ^ 2 ≤ N := fun i => by
    rw [hN, dotProduct, sq]
    exact Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)
  have h1 : c * N ≤ u k := by
    have := hY u
    rwa [hYu, dotProduct_single, mul_one] at this
  have huk : 0 ≤ u k := le_trans (mul_nonneg hc.le hN0) h1
  have h2 : c ^ 2 * N ^ 2 ≤ N := by
    calc c ^ 2 * N ^ 2 = (c * N) ^ 2 := by ring
      _ ≤ u k ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le hN0) h1 2
      _ ≤ N := hcomp k
  have h3 : c ^ 2 * N ≤ 1 := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  have h4 : (c * u j) ^ 2 ≤ 1 := by
    calc (c * u j) ^ 2 = c ^ 2 * u j ^ 2 := by ring
      _ ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg c)
      _ ≤ 1 := h3
  rw [hentry, le_div_iff₀ hc, mul_comm]
  have := (sq_le_one_iff_abs_le_one _).1 h4
  rwa [abs_mul, abs_of_pos hc] at this

end GlobalTheory.ConnPointwise

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs

end GlobalTheory.ConnPointwise

namespace GlobalTheory

open GlobalTheory.ConnPointwise

theorem connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApply
section
noncomputable section

open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

omit [Fintype l] in
theorem continuous_pPart : Continuous (pPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold pPart
  fun_prop

omit [Fintype l] in
theorem continuous_qPart : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold qPart
  fun_prop

theorem continuous_inner_rho_schwartz (φ f : Sch l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ = ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_rho w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _) (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_phase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_phase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, phase]
    have := continuous_pPart (l := l)
    have := continuous_qPart (l := l)
    fun_prop

theorem continuous_rho_schwartz (f : Sch l) : Continuous fun w : l ⊕ l → ℝ => rho w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : L2 l := f.toLp 2 with hv
  set g : L2 l := (rhoSch w₀ f).toLp 2 with hg
  have h0 : rho w₀ v = g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_rho w₀ (f.toLp 2), rhoFun_congr w₀ (f.coeFn_toLp 2 volume),
      (rhoSch w₀ f).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, coe_rhoSch]
  have hsq : ∀ w, ‖rho w v - rho w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, rho w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖rho w v - rho w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul (continuous_re.comp (continuous_inner_rho_schwartz (rhoSch w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

theorem continuous_rho_prod : Continuous fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith (fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_rho_schwartz f) fun w => (rho w).lipschitz

theorem continuous_rho : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v :=
  fun l _ v => (continuous_rho_prod (l := l)).comp (f := fun w : l ⊕ l → ℝ => ((v, w) : L2 l × (l ⊕ l → ℝ)))
    (Continuous.prodMk continuous_const continuous_id)

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeUnitEtaleExtension
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coprime_unit_etale_extension : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (exact GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (intros; apply GlobalTheory.EtC.unit_isPow_on_excisionNbhd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosimplicialSesExactAtSucc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cosimplicial_ses_exactAt_succ :
    ∀ (Z M Q : CosimplicialObject AddCommGrpCat.{1}) (i : Z ⟶ M) (p : M ⟶ Q), (∀ k, Function.Injective (i.app k)) → (∀ k (y : M.obj k), p.app k y = 0 ↔ ∃ w, i.app k w = y) → (∀ k, Function.Surjective (p.app k)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Z).ExactAt (n + 1)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj M).ExactAt (n + 1)) → ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Q).ExactAt (n + 1) := by
  intro Z M Q i p hinj hex hsurj h₁ h₂
  let F := AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}
  have hw : F.map i ≫ F.map p = 0 := by
    ext k y
    exact (hex _ (i.app _ y)).2 ⟨y, rfl⟩
  let T : ShortComplex (CochainComplex AddCommGrpCat.{1} ℕ) := ShortComplex.mk (F.map i) (F.map p) hw
  have hT : T.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.ab_exact_iff]; intro x hx; exact (hex _ x).1 hx
    · rw [AddCommGrpCat.mono_iff_injective]; exact hinj _
    · rw [AddCommGrpCat.epi_iff_surjective]; exact hsurj _
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have e := hT.homology_exact₃ (n + 1) (n + 2) rfl
  have z2 : IsZero (T.X₂.homology (n + 1)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)
  have z1 : IsZero (T.X₁.homology (n + 2)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))
  exact e.isZero_X₂ (z2.eq_of_src _ _) (z1.eq_of_tgt _ _)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineSquarePushforwardUniformStatement
section
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_square_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool), G.PosDef →
    Measure.map (GlobalTheory.LineCos.cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (GlobalTheory.LineCos.hform G (GlobalTheory.LineCos.lineVec s x) (GlobalTheory.LineCos.lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.FsLaw.map_cosSq_fs | exact GlobalTheory.LineCos.FsLaw.map_cosSq_fs | (intros; apply GlobalTheory.LineCos.FsLaw.map_cosSq_fs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConerveProperty
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem refines_of_coAug : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Cov : MorphismProperty T) (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop), (∀ (U V : T) (g : U ⟶ V), Cov g → Q U _ (coAug g)) → Refines Cov Q := by
  intro T _ _ Cov Q hQ U V g hg
  refine ⟨_, coAug g, WidePushout.ι (fun _ : Fin 1 => g) 0, ?_, hQ U V g hg⟩
  exact WidePushout.arrow_ι (fun _ : Fin 1 => g) 0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicTorsorEtale
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_torsor_etale : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act → Algebra.Etale B D := by
  first | (exact @GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (exact GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (intros; apply GlobalTheory.KeyOriginCut.etale_of_isZTorsor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGenMatIsHomogeneous
section
open IsLocalRing

namespace GlobalTheory.ReducedNormExists

open MvPolynomial TensorProduct

noncomputable abbrev genMat {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (MvPolynomial ι R) :=
  ∑ i, (X i : MvPolynomial ι R) • (M i).map (C : R →+* MvPolynomial ι R)

theorem isUnit_one_tmul_iff {K E B : Type} [Field K] [Field E] [Algebra K E] [Ring B]
    [Algebra K B] [FiniteDimensional K B] (x : B) :
    IsUnit ((1 : E) ⊗ₜ[K] x) ↔ IsUnit x := by
  constructor
  · intro hu
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[K] E ⊗[K] B) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap K E).injective
    have hL : Function.Injective (LinearMap.mulLeft K x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have h0 : ((1 : E) ⊗ₜ[K] x) * (1 ⊗ₜ z) = 0 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [LinearMap.mulLeft_apply] at hz
        rw [hz, TensorProduct.tmul_zero]
      have h1 : (1 : E) ⊗ₜ[K] z = 0 := hu.mul_right_eq_zero.mp h0
      exact hinj (by simpa using h1)
    have hR : Function.Injective (LinearMap.mulRight K x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have h0 : ((1 : E) ⊗ₜ[K] z) * (1 ⊗ₜ x) = 0 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [LinearMap.mulRight_apply] at hz
        rw [hz, TensorProduct.tmul_zero]
      have h1 : (1 : E) ⊗ₜ[K] z = 0 := hu.mul_left_eq_zero.mp h0
      exact hinj (by simpa using h1)
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hL 1
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hR 1
    simp only [LinearMap.mulLeft_apply] at hz
    simp only [LinearMap.mulRight_apply] at hw
    have hwz : w = z := by
      calc w = w * (x * z) := by rw [hz, mul_one]
        _ = (w * x) * z := (mul_assoc _ _ _).symm
        _ = z := by rw [hw, one_mul]
    exact ⟨⟨x, z, hz, hwz ▸ hw⟩, rfl⟩
  · intro hx
    exact hx.map (Algebra.TensorProduct.includeRight : B →ₐ[K] E ⊗[K] B)

end GlobalTheory.ReducedNormExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangularStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  first | (exact @GlobalTheory.Shin.BlocksTwist.blocks_twist) | (exact GlobalTheory.Shin.BlocksTwist.blocks_twist) | (intros; apply GlobalTheory.Shin.BlocksTwist.blocks_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityOfVanishingPowersStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_of_vanishing_powers : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  first | exact @GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow | exact GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow | (intros; apply GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow <;> assumption)
end

