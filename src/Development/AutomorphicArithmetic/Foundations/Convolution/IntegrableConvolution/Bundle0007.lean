import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
section
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private lemma fib_cons {m : ℕ} (a : G) (y : Fin m → G) (x : G) :
    fib (Fin.cons (α := fun _ => G) a y) x = Fin.cons (α := fun _ => G) a (fib y (a⁻¹ * x)) := by
  unfold fib
  rw [← Fin.cons_snoc_eq_snoc_cons]
  congr 2
  simp [List.ofFn_succ, mul_assoc]

private lemma continuous_fib {m : ℕ} (x : G) : Continuous fun y : Fin m → G => fib y x := by
  have hp : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply i
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact (hp.inv).mul continuous_const
  · simp only [fib, Fin.snoc_castSucc]
    exact continuous_apply j

private lemma integrable_fib (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hc : ∀ i, Continuous (φ i)) (hs : ∀ i, HasCompactSupport (φ i)) (x : G) :
    Integrable (fun y : Fin m → G => ∏ i, φ i (fib y x i)) (Measure.pi fun _ => μ) := by
  have hcont : Continuous fun y : Fin m → G => ∏ i, φ i (fib y x i) :=
    continuous_finset_prod _ fun i _ =>
      (hc i).comp ((continuous_apply i).comp (continuous_fib x))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    (K := Set.pi Set.univ fun i : Fin m => tsupport (φ i.castSucc))
    (isCompact_univ_pi fun i => hs _) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i.castSucc) ?_
  simp only [fib, Fin.snoc_castSucc]
  exact image_eq_zero_of_notMem_tsupport hi

private lemma push_tens (μ : Measure G) [μ.IsHaarMeasure] : ∀ (m : ℕ) (φ : Fin (m + 1) → G → ℂ),
    (∀ i, Continuous (φ i)) → (∀ i, HasCompactSupport (φ i)) →
    push μ m (fun g => ∏ i, φ i (g i)) = cvAll μ m φ := by
  intro m
  induction m with
  | zero =>
    intro φ _ _
    funext x
    simp [push, cvAll, fib, Measure.real, Measure.pi_empty_univ, Fin.snoc]
  | succ m ih =>
    intro φ hc hs
    funext x
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hint := integrable_fib μ (m + 1) φ hc hs x
    set F : (Fin (m + 1) → G) → ℂ := fun y => ∏ i, φ i (fib y x i) with hF
    have hsymm := hmp.symm
    have hint' : Integrable (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm)
        (μ.prod (Measure.pi fun _ => μ)) :=
      (hsymm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
    have hval : ∀ (a : G) (y : Fin m → G),
        (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm) (a, y) =
          φ 0 a * ∏ i, Fin.tail φ i (fib y (a⁻¹ * x) i) := by
      intro a y
      have : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm (a, y) =
          Fin.cons (α := fun _ => G) a y := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
      simp only [Function.comp, this, hF, fib_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    show ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    refine (hsymm.integral_comp' F).symm.trans ((integral_prod _ hint').trans ?_)
    simp only [cvAll, cv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hval, integral_const_mul]
    have := congrFun (ih (Fin.tail φ) (fun i => hc _) (fun i => hs _)) (a⁻¹ * x)
    rw [← this]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.pushTens :
    UpperTheory.ConvolutionTheory.L1.PushTens := by
  intro G _ _ _ _ _ _ _ _ μ _ m φ hc hs
  exact UpperTheory.ConvolutionTheory.L1.push_tens μ m φ hc hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
section
open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => Polynomial.coeff p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

private theorem ev_val (i : I) (g : GL (Fin n) (∀ i, k i)) :
    ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) =
      (g : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i) := rfl

private theorem ev_ext {g h : GL (Fin n) (∀ i, k i)} (e : ∀ i, ev i g = ev i h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
  have h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b =
      ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b := by rw [e i]
  exact h

private def asm (x : ∀ i, GL (Fin n) (k i)) : GL (Fin n) (∀ i, k i) where
  val := Matrix.of fun a b i => (x i : Matrix (Fin n) (Fin n) (k i)) a b
  inv := Matrix.of fun a b i => ((x i)⁻¹ : GL (Fin n) (k i)).val a b
  val_inv := by
    ext a b i
    have h := congrFun (congrFun (x i).val_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b i
    have h := congrFun (congrFun (x i).inv_val a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

private theorem ev_asm (x : ∀ i, GL (Fin n) (k i)) (i : I) : ev i (asm x) = x i := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

end Pi

private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    rw [ev_val, Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))
  refine ⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨asm x, ev_ext fun i => ?_⟩
        simp only [map_mul, map_inv, ev_asm]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    rw [map_mul, map_mul]
    refine centComm_field (ev i γ) _ _ (hsi i) ?_ ?_
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ha, map_mul]
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hb, map_mul]

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
end

