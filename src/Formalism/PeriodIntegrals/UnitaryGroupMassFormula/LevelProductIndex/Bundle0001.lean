import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development
import Formalism.SatakeDualWeyl.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVMemTensInt
section
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

noncomputable section

namespace PI.LPI

theorem prV_tmul' {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

theorem prV_mem_tensInt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  have hle : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (v.adicCompletion F) (intOE E)
        (v.adicCompletionIntegers F).toSubring).comap (prV (E := E) v) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · change prV (E := E) v ((x : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inl ⟨x, rfl⟩)
    · change prV (E := E) v ((1 : E) ⊗ₜ[F] (a : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inr ⟨⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩, rfl⟩)
  exact hle hs

theorem plDown : PLDown := by
  intro F E _ _ _ _ _ n Lb v y hy
  have hy' : y ∈ Submodule.span (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      ((fun x : Fin n → E => fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ''
        (Lb : Set (Fin n → E))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨l, hl, rfl⟩
  | zero =>
    convert (latV v Lb).zero_mem using 1
    funext j
    simp
  | add x y _ _ hx hy =>
    have h : (fun j => prV (E := E) v ((x + y) j)) =
        (fun j => prV (E := E) v (x j)) + (fun j => prV (E := E) v (y j)) := by
      funext j; simp
    rw [h]
    exact add_mem hx hy
  | smul s x _ hx =>
    have h : (fun j => prV (E := E) v ((s • x) j)) =
        (⟨prV (E := E) v s, prV_mem_tensInt (E := E) v s s.2⟩ :
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) •
          (fun j => prV (E := E) v (x j)) := by
      funext j
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j) = prV (E := E) v s * prV (E := E) v (x j)
      exact map_mul _ _ _
    rw [h]
    exact Submodule.smul_mem _ _ hx

end PI.LPI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVSumTmul
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    ∃ (k : ℕ) (m : Fin k → Fin n → E), (∀ i, m i ∈ Lb) ∧
      (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) := by
  have : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  refine ⟨k, fun i => (s i : Fin n → E), fun i => (s i).2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨z, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [Submodule.coe_sum] at h2
  exact h2.symm

theorem prV_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] a v := by
  simp [prV, evalV, Algebra.TensorProduct.map_tmul]
  rfl

theorem prV_sum_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (e : Fin k → E) (a : Fin k → FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (∑ i, e i ⊗ₜ[F] a i) = ∑ i, e i ⊗ₜ[F] a i v := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => prV_tmul v (e i) (a i)

def adOf {F : Type} [Field F] [NumberField F] (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  (⟨a, Filter.Eventually.of_forall ha⟩ :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem adOf_apply {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    adOf a ha v = a v := rfl

theorem adOf_mem {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : adOf a ha ∈ intAd F := fun v => ha v

theorem plUp_of (hG : PLGen) (hI : PLInj) : PLUp := by
  intro F E _ _ _ _ _ n Lb hfin y hy
  obtain ⟨k, m, hm, hgen⟩ := exists_gen Lb hfin
  have hloc := fun v : HeightOneSpectrum (𝓞 F) =>
    (hG F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Lb m hm hgen
      (fun j => prV (E := E) v (y j))).1 (hy v)
  choose a ha hya using hloc
  let A : Fin k → FiniteAdeleRing (𝓞 F) F := fun i => adOf (fun v => a v i) (fun v => ha v i)
  have hyA : (fun j => ∑ i, m i j ⊗ₜ[F] A i) ∈ latA F Lb :=
    (hG F E (FiniteAdeleRing (𝓞 F) F) (intAd F) n k Lb m hm hgen _).2
      ⟨A, fun i => adOf_mem _ _, rfl⟩
  have hyy : y = fun j => ∑ i, m i j ⊗ₜ[F] A i := by
    funext j
    refine sub_eq_zero.1 (hI F E _ fun v => ?_)
    rw [map_sub, sub_eq_zero, prV_sum_tmul]
    exact congrFun (hya v) j
  rw [hyy]
  exact hyA

end PI.LPI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVTmulEqTmulApply
section
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

noncomputable section

namespace PI.LPI

theorem prV_tmul_eq_tmul_apply {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

theorem coord_prV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {ι : Type}
    [DecidableEq ι] (b : Module.Basis ι F E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (prV (E := E) v z) i =
      (TensorProduct.equivFinsuppOfBasisLeft b z i) v := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]; try rfl
  | tmul e a =>
    rw [prV_tmul_eq_tmul_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp only [Algebra.smul_def]
    rfl
  | add x y hx hy =>
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx, hy]
    try rfl

theorem plInj : PLInj := by
  intro F E _ _ _ _ _ z hz
  let b := Module.finBasis F E
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  refine Finsupp.ext fun i => FiniteAdeleRing.ext F fun v => ?_
  rw [← coord_prV b v z i, hz v, map_zero]
  rfl

end PI.LPI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.LevelProdIdx

open Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}

def latSet (R : Type) [CommRing R] [Algebra F R] (O : Subring R) {k : ℕ} (G : Fin k → (Fin n → E)) :
    Set (Fin n → E ⊗[F] R) :=
  {y | ∃ c : Fin k → R, (∀ i, c i ∈ O) ∧ y = fun l => ∑ i, G i l ⊗ₜ[F] c i}

section Set

variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}

theorem zero_mem_latSet : (0 : Fin n → E ⊗[F] R) ∈ latSet R O G := ⟨0, fun _ => O.zero_mem, by funext l; simp⟩

theorem add_mem_latSet {y z : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) (hz : z ∈ latSet R O G) :
    y + z ∈ latSet R O G := by
  obtain ⟨c, hc, rfl⟩ := hy
  obtain ⟨c', hc', rfl⟩ := hz
  refine ⟨c + c', fun i => O.add_mem (hc i) (hc' i), ?_⟩
  funext l
  simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem neg_mem_latSet {y : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) :
    -y ∈ latSet R O G := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨-c, fun i => O.neg_mem (hc i), ?_⟩
  funext l
  simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem smul_mem_latSet [NumberField E]
    (hG : ∀ i (o : 𝓞 E), ∃ z : Fin k → ℤ, ∀ l, (o : E) * G i l = ∑ j, z j • G j l)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) :
    ∀ y : Fin n → E ⊗[F] R, y ∈ latSet R O G → s • y ∈ latSet R O G := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rintro y ⟨c, hc, rfl⟩
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨d, hd⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      choose z hz using fun i => hG i o
      refine ⟨fun j => ∑ i, z i j • c i, fun j => sum_mem fun i _ => zsmul_mem (hc i) _, ?_⟩
      ext l
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, hz, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    · refine ⟨fun i => d * c i, fun i => mul_mem hd (hc i), ?_⟩
      ext l
      simp [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => intro y _; rw [zero_smul]; exact zero_mem_latSet
  | one => intro y hy; rwa [one_smul]
  | add a b _ _ ha hb => intro y hy; rw [add_smul]; exact add_mem_latSet (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [neg_smul]; exact neg_mem_latSet (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)

end Set

variable [NumberField E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (O : Subring R)
    (Λ : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (G : Fin k → (Fin n → E)) (hGm : ∀ i, G i ∈ Λ)
    (hΛ : ∀ x ∈ Λ, ∃ z : Fin k → ℤ, x = ∑ j, z j • G j) (y : Fin n → E ⊗[F] R) :
    y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ ↔ y ∈ latSet R O G := by
  have hG : ∀ i (o : 𝓞 E), ∃ z : Fin k → ℤ, ∀ l, (o : E) * G i l = ∑ j, z j • G j l := by
    intro i o
    obtain ⟨z, hz⟩ := hΛ _ (Λ.smul_mem o (hGm i))
    refine ⟨z, fun l => ?_⟩
    calc (o : E) * G i l = (o • G i) l := rfl
      _ = _ := by rw [hz]; simp [Finset.sum_apply]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨z, rfl⟩ := hΛ x hx
      refine ⟨fun j => ((z j : R)), fun j => intCast_mem _ _, ?_⟩
      ext l
      simp only [inclE, Finset.sum_apply, Pi.smul_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
        TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    | zero => exact zero_mem_latSet
    | add a b _ _ ha hb => exact add_mem_latSet ha hb
    | smul a x _ hx => exact smul_mem_latSet hG a.2 x hx
  · rintro ⟨c, hc, rfl⟩
    have : (fun l => ∑ i, G i l ⊗ₜ[F] c i) =
        ∑ i, (⟨(1 : E) ⊗ₜ[F] c i, Subring.subset_closure (Or.inr ⟨⟨c i, hc i⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) O) • (fun l => inclE (F := F) R (G i l)) := by
      ext l
      simp [Finset.sum_apply, inclE, Algebra.TensorProduct.tmul_mul_tmul, Subring.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨G i, hGm i, rfl⟩)

end PI.UnitaryGroupMassFormula.LevelProdIdx

namespace PI.LPI

theorem plGen : PLGen := by
  intro F E _ _ _ _ _ R _ _ O n k Lb m hm hLb y
  exact PI.UnitaryGroupMassFormula.LevelProdIdx.mem_latS_iff R O Lb m hm hLb y

end PI.LPI
end
end

