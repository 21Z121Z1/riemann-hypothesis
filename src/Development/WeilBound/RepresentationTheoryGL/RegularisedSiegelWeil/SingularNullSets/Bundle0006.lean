import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]

variable (F E) in

abbrev bE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

abbrev bV (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (bE F E)

theorem bV_apply (v : HeightOneSpectrum (𝓞 F)) (k : Fin (Module.finrank F E)) : bV (E := E) v k = 1 ⊗ₜ[F] bE F E k :=
  Algebra.TensorProduct.basis_apply _ _

theorem crd_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) (k : Fin (Module.finrank F E)) :
    (bV v).repr (a ⊗ₜ[F] e) k = a * algebraMap F (Fv F v) ((bE F E).repr e k) := by
  simp [bV, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem exists_den (x : E) : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

def den (x : E) : ℤ := Classical.choose (exists_den x)

theorem den_ne (x : E) : den x ≠ 0 := (Classical.choose_spec (exists_den x)).1

theorem den_int (x : E) : IsIntegral ℤ ((den x : E) * x) := (Classical.choose_spec (exists_den x)).2

variable (F E) in

def trM : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F := fun i j => Algebra.trace F E (bE F E i * bE F E j)

theorem trM_det : (trM F E).det ≠ 0 := by
  have h := Algebra.discr_not_zero_of_basis F (bE F E)
  rw [Algebra.discr_def] at h
  convert h using 2
  ext i j
  simp [trM, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

def IsGood (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)),
      algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F) ∧
    algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F

theorem eventually_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

theorem eventually_good : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsGood F E v :=
  (eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and (eventually_int _))))

theorem eventually_coord (y : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ k, algebraMap F (Fv F v) ((bE F E).repr y k) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun _ => eventually_int _

variable {v : HeightOneSpectrum (𝓞 F)}

theorem IsGood.half (hv : IsGood F E v) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := hv.2.2.2.2

theorem IsGood.ogen (hv : IsGood F E v) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
  hv.1 l k

theorem IsGood.deninv (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F := hv.2.1 k

theorem IsGood.trinv (hv : IsGood F E v) (i j : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F := hv.2.2.1 i j

theorem IsGood.trb (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F := hv.2.2.2.1 k

theorem one_tmul_b_mem (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    (1 : Fv F v) ⊗ₜ[F] bE F E k ∈ intLoc F E v := by
  have hN : (den (bE F E k) : F) ≠ 0 := by exact_mod_cast den_ne (bE F E k)
  let o : 𝓞 E := ⟨(den (bE F E k) : E) * bE F E k, den_int (bE F E k)⟩
  have ho : (o : E) = (den (bE F E k) : E) * bE F E k := rfl
  have e : (1 : Fv F v) ⊗ₜ[F] bE F E k = algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ⊗ₜ[F] (o : E) := by
    rw [ho]
    have : ((den (bE F E k) : E) * bE F E k) = (den (bE F E k) : F) • bE F E k := by
      rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hN,
      map_one]
  rw [e]
  exact tmul_mem_intLoc (hv.deninv k) o

theorem tmul_one_mem {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) ha (1 : 𝓞 E)

theorem mem_intLoc_iff (hv : IsGood F E v) (z : Fv F v ⊗[F] E) :
    z ∈ intLoc F E v ↔ ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hz
    refine intLoc_induction (p := fun z => ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F) (fun a ha x k => ?_)
      (fun k => by simp) (fun y z hy hz k => by rw [map_add, Finsupp.add_apply]; exact add_mem (hy k) (hz k))
      (fun y hy k => by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)) hz
    rw [crd_tmul]
    refine mul_mem ha ?_
    let L : 𝓞 E →+ F := ((Finsupp.applyAddHom k).comp (bE F E).repr.toLinearMap.toAddMonoidHom).comp
      (algebraMap (𝓞 E) E).toAddMonoidHom
    have e : L x = ∑ l, ((RingOfIntegers.basis E).repr x l) • L (RingOfIntegers.basis E l) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      rw [map_sum]
      simp only [map_zsmul]
    change algebraMap F (Fv F v) (L x) ∈ _
    rw [e, map_sum]
    refine sum_mem fun l _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (hv.ogen l k) _
  · intro h
    rw [← (bV v).sum_repr z]
    refine sum_mem fun k _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : (bV v).repr z k ⊗ₜ[F] bE F E k = ((bV v).repr z k ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] bE F E k) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact mul_mem (tmul_one_mem (h k)) (one_tmul_b_mem hv k)

theorem trace_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F (Fv F v) (Algebra.trace F E e) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (bV v), Algebra.trace_eq_matrix_trace (bE F E), Matrix.trace, Matrix.trace,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    bV_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, crd_tmul]

theorem trace_eq_sum (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z =
      ∑ k, (bV v).repr z k * algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) := by
  conv_lhs => rw [← (bV v).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, trace_tmul]

theorem trace_mem (hv : IsGood F E v) {z : Fv F v ⊗[F] E} (hz : z ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  rw [trace_eq_sum]
  exact sum_mem fun k _ => mul_mem (((mem_intLoc_iff hv z).1 hz) k) (hv.trb k)

theorem mem_of_trace (hv : IsGood F E v) (c : Fv F v ⊗[F] E)
    (h : ∀ t ∈ intLoc F E v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * t) ∈ v.adicCompletionIntegers F) :
    c ∈ intLoc F E v := by
  classical
  set u : Fin (Module.finrank F E) → Fv F v := fun j => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (1 ⊗ₜ[F] bE F E j))
  have hu : ∀ j, u j ∈ v.adicCompletionIntegers F := fun j => h _ (one_tmul_b_mem hv j)
  have hu' : ∀ j, u j = ∑ l, (bV v).repr c l * algebraMap F (Fv F v) (trM F E l j) := by
    intro j
    simp only [u]
    conv_lhs => rw [← (bV v).sum_repr c]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      trace_tmul]
    rfl
  have hT : trM F E * (trM F E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 trM_det)
  refine (mem_intLoc_iff hv c).2 fun k => ?_
  have e : (bV v).repr c k = ∑ j, u j * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) := by
    have h1 : ∀ l, ∑ j, algebraMap F (Fv F v) (trM F E l j) * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) =
        if l = k then 1 else 0 := by
      intro l
      have := congrFun (congrFun hT l) k
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp_rw [← map_mul, ← map_sum, this]
      split_ifs <;> simp
    simp_rw [hu', Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h1]
    simp
  rw [e]
  exact sum_mem fun j _ => mul_mem (hu j) (hv.trinv j k)

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKC
section
noncomputable section

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, finEmb_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_mem (σ : E →ₐ[F] E) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : sigR (Fv F v) σ y ∈ intLoc F E v := sigR_mem_intLoc σ hy

def sR (σ : E →ₐ[F] E) : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict (intLoc F E v) fun y => sigR_mem v σ y.2

@[simp] theorem coe_sR (σ : E →ₐ[F] E) (y : intLoc F E v) : (sR v σ y : Fv F v ⊗[F] E) = sigR (Fv F v) σ y := rfl

theorem absBar_le_one (τ : E →ₐ[F] FvBar F v) (y : intLoc F E v) : absBar F v (finEmb F v τ y) ≤ 1 := (le_absFin F v τ y).trans (absFin_le_one_of_mem_intLoc y.2)

def p0 (τ : E →ₐ[F] FvBar F v) : Ideal (intLoc F E v) where
  carrier := {y | absBar F v (finEmb F v τ y) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add, map_add] at *
    exact (absBar_add_le F v _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
    rw [(absBar_eq_zero F v).2 rfl]; exact zero_lt_one
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul, absBar_mul] at *
    calc absBar F v (finEmb F v τ c) * absBar F v (finEmb F v τ y) ≤ 1 * absBar F v (finEmb F v τ y) :=
          mul_le_mul_of_nonneg_right (absBar_le_one v τ c) zero_le
      _ < 1 := by rw [one_mul]; exact hy

theorem absBar_finEmb_one (τ : E →ₐ[F] FvBar F v) : absBar F v (finEmb F v τ 1) = 1 := by
  rw [map_one]; simpa using absBar_algebraMap F v 1

theorem prime_valuation_ne_top (τ : E →ₐ[F] FvBar F v) : p0 v τ ≠ ⊤ := by
  intro h
  have : (1 : intLoc F E v) ∈ p0 v τ := h ▸ Submodule.mem_top
  change absBar F v (finEmb F v τ ((1 : intLoc F E v) : Fv F v ⊗[F] E)) < 1 at this
  rw [OneMemClass.coe_one, absBar_finEmb_one] at this
  exact lt_irrefl _ this

theorem isUnit_of_absBar (y : intLoc F E v) (h : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ y) = 1) :
    IsUnit y := by
  have hne : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ (y : Fv F v ⊗[F] E) ≠ 0 := by
    intro τ h0
    have h1 := h τ
    rw [h0, (absBar_eq_zero F v).2 rfl] at h1
    exact zero_ne_one h1
  have hinj : Function.Injective (LinearMap.mulLeft (Fv F v) (y : Fv F v ⊗[F] E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [LinearMap.mulLeft_apply] at hz
    apply absFin_eq_zero_iff.1
    refine le_antisymm (Finset.sup_le fun τ _ => ?_) bot_le
    have h1 := congrArg (finEmb F v τ) hz
    rw [map_mul, map_zero] at h1
    rw [le_zero_iff, absBar_eq_zero]
    exact (mul_eq_zero.1 h1).resolve_left (hne τ)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  rw [LinearMap.mulLeft_apply] at hz
  have hzmem : z ∈ intLoc F E v := by
    rw [mem_intLoc_iff_absFin_le_one]
    refine Finset.sup_le fun τ _ => ?_
    have e1 := absBar_finEmb_one v τ
    have h1 := congrArg (fun w => absBar F v (finEmb F v τ w)) hz
    simp only [map_mul, absBar_mul, h τ, one_mul] at h1
    rw [h1, e1]
  exact isUnit_iff_exists_inv.2 ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

theorem emb_cases (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) (τ0 τ : E →ₐ[F] FvBar F v) :
    τ = τ0 ∨ τ = τ0.comp σ := by
  classical
  by_contra hne
  push_neg at hne
  have hd : τ0 ≠ τ0.comp σ := by
    intro h
    apply hσ1
    ext x
    have hx : τ0 x = τ0 (σ x) := congrArg (fun g => g x) h
    exact (τ0.injective hx).symm
  have hc := card_algHom_le_finrank F E (FvBar F v)
  rw [h2, ← Fintype.card_eq_nat_card] at hc
  have h3 : ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hd]
    simp [hne.1, hne.2]
  have h4 := Finset.card_le_univ ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v))
  omega

theorem exists_max (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) :
    ∃ 𝔭 : Ideal (intLoc F E v), 𝔭.IsMaximal ∧ ∀ x, x ∉ 𝔭 → sR v σ x ∉ 𝔭 → IsUnit x := by
  have τ0 : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal _ (prime_valuation_ne_top v τ0)
  refine ⟨𝔭, hmax, fun x hx hsx => isUnit_of_absBar v x fun τ => ?_⟩
  have hone : ∀ w : intLoc F E v, w ∉ 𝔭 → absBar F v (finEmb F v τ0 w) = 1 := by
    intro w hw
    exact le_antisymm (absBar_le_one v τ0 w) (not_lt.1 fun hlt => hw (hle (show w ∈ p0 v τ0 from hlt)))
  rcases emb_cases v σ hσ1 h2 τ0 τ with rfl | rfl
  · exact hone x hx
  · have h5 := hone _ hsx
    rwa [coe_sR, finEmb_sigR] at h5

theorem isUnit_two (h : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : intLoc F E v) := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = ((2 : F) : Fv F v) := by
      rw [show (2 : F) = 1 + 1 by norm_num, HeightOneSpectrum.adicCompletion.coe_add,
        HeightOneSpectrum.adicCompletion.coe_one]
      norm_num
    have e2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat (algebraMap (𝓞 F) F) 2).symm
    rw [e, HeightOneSpectrum.adicCompletion.valued_coe, e2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact h
  have hmem : (2 : Fv F v)⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have h0 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have h2 : (2 : Fv F v ⊗[F] E) = (2 : Fv F v) ⊗ₜ[F] (1 : E) := by
    rw [show (2 : Fv F v) = 1 + 1 by norm_num, TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    norm_num
  have hc : ((2 : intLoc F E v) : Fv F v ⊗[F] E) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  refine isUnit_iff_exists_inv.2 ⟨⟨_, tmul_mem_intLoc hmem (1 : 𝓞 E)⟩, Subtype.ext ?_⟩
  push_cast
  rw [hc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ h0, one_mul,
    ← Algebra.TensorProduct.one_def]

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvA
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm

open Classical in

def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem indS_apply (S : Finset (Pl D)) (v : Pl D) : (indS S) v = if v ∈ S then 1 else 0 := rfl

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem infPart_eS (S : Finset (Pl D)) : infPart D (eS S) = 1 := by
  simp only [infPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

theorem finPart_eS (S : Finset (Pl D)) :
    finPart D (eS S) = algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) := by
  simp only [finPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem cv_eq (v : Pl D) (z : AE D) :
    cv D v z = Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add, hx, hy, RingHom.map_add, map_add]
  | tmul a x => rfl

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

