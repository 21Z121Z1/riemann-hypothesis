import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjTDefs
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

def TraceBase : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E),
    Algebra.trace R (R ⊗[F] E) (hR R σ J (ratV (F := F) R x) (ratV (F := F) R y)) =
      algebraMap F R (Algebra.trace F E (hE σ J x y))

def TraceGramND : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (k : ℕ) (b : Module.Basis (Fin k) F (Fin M → E)),
      (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))).det ≠ 0

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HasStableRangeOne
section
noncomputable section

namespace PI.VolSemiDirect.W.SR

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct

theorem sr1_prod {A B : Type} [CommRing A] [CommRing B] (hA : Cj.HasStableRangeOne A) (hB : Cj.HasStableRangeOne B) :
    Cj.HasStableRangeOne (A × B) := by
  intro a b x y h
  obtain ⟨t1, ht1⟩ := hA a.1 b.1 x.1 y.1 (by simpa using congrArg Prod.fst h)
  obtain ⟨t2, ht2⟩ := hB a.2 b.2 x.2 y.2 (by simpa using congrArg Prod.snd h)
  exact ⟨(t1, t2), Prod.isUnit_iff.2 ⟨ht1, ht2⟩⟩

theorem stable_rank_one_pi_field {ι : Type} {K : ι → Type} [∀ i, Field (K i)] : Cj.HasStableRangeOne (∀ i, K i) := by
  classical
  intro a b x y h
  refine ⟨fun i => if a i = 0 then 1 else 0, Pi.isUnit_iff.2 fun i => ?_⟩
  have hi : a i * x i + b i * y i = 1 := by simpa using congrFun h i
  by_cases ha : a i = 0
  · have hb : b i ≠ 0 := by
      rintro hb
      simp [ha, hb] at hi
    simp [ha, hb]
  · simp [ha]

theorem pt_ne {K : Type} [Field K] (B : ValuationSubring K) {a b x y : K} (h : a * x + b * y = 1) :
    a + (if B.valuation b ≤ B.valuation a then 0 else 1) * b ≠ 0 := by
  split_ifs with hv
  · rw [zero_mul, add_zero]
    rintro rfl
    have hb0 : B.valuation b = 0 := le_antisymm (by simpa using hv) zero_le'
    rw [Valuation.zero_iff] at hb0
    subst hb0
    simp at h
  · rw [one_mul]
    intro hab
    apply hv
    have : b = -a := by linear_combination hab
    rw [this, Valuation.map_neg]

theorem pt_unit {K : Type} [Field K] (B : ValuationSubring K) {a b x y : K}
    (h : a * x + b * y = 1) (ha : a ∈ B) (hb : b ∈ B) (hx : x ∈ B) (hy : y ∈ B) :
    ∃ hm : a + (if B.valuation b ≤ B.valuation a then 0 else 1) * b ∈ B,
      IsUnit (⟨_, hm⟩ : B) := by
  have hv1 : ∀ z ∈ B, B.valuation z ≤ 1 := fun z hz => (B.valuation_le_one_iff z).2 hz
  have hone : 1 ≤ max (B.valuation a) (B.valuation b) := by
    have := Valuation.map_add B.valuation (a * x) (b * y)
    rw [h, map_one] at this
    refine this.trans (max_le_max ?_ ?_)
    · rw [map_mul]
      exact mul_le_of_le_one_right' (hv1 x hx)
    · rw [map_mul]
      exact mul_le_of_le_one_right' (hv1 y hy)
  split_ifs with hv
  · refine ⟨by rw [zero_mul, add_zero]; exact ha, (B.valuation_eq_one_iff _).2 ?_⟩
    show B.valuation (a + 0 * b) = 1
    rw [zero_mul, add_zero]
    exact le_antisymm (hv1 a ha) (by rwa [max_eq_left hv] at hone)
  · have hlt : B.valuation a < B.valuation b := not_le.1 hv
    refine ⟨by rw [one_mul]; exact add_mem ha hb, (B.valuation_eq_one_iff _).2 ?_⟩
    show B.valuation (a + 1 * b) = 1
    rw [one_mul, Valuation.map_add_eq_of_lt_right _ hlt]
    exact le_antisymm (hv1 b hb) (by rwa [max_eq_right hlt.le] at hone)

theorem stable_rank_one_restricted_product {ι : Type} {R : ι → Type} [∀ i, Field (R i)] (B : ∀ i, ValuationSubring (R i)) :
    Cj.HasStableRangeOne (Πʳ i, [R i, B i]) := by
  classical
  intro a b x y h
  have hi : ∀ i, a i * x i + b i * y i = 1 := fun i => by
    have := congrArg (fun z : Πʳ i, [R i, B i] => z i) h
    simpa using this
  let tf : ∀ i, R i := fun i => if (B i).valuation (b i) ≤ (B i).valuation (a i) then 0 else 1
  have ht : ∀ᶠ i in Filter.cofinite, tf i ∈ ((B i : ValuationSubring (R i)) : Set (R i)) :=
    Filter.Eventually.of_forall fun i => by
      simp only [tf]
      split_ifs
      · exact (B i).zero_mem
      · exact (B i).one_mem
  have hne : ∀ i, a i + tf i * b i ≠ 0 := fun i => pt_ne (B i) (hi i)
  have hev : ∀ᶠ i in Filter.cofinite, a i ∈ B i ∧ b i ∈ B i ∧ x i ∈ B i ∧ y i ∈ B i :=
    a.2.and (b.2.and (x.2.and y.2))
  have hu : ∀ᶠ i in Filter.cofinite,
      (a i + tf i * b i)⁻¹ ∈ ((B i : ValuationSubring (R i)) : Set (R i)) :=
    hev.mono fun i ⟨ha, hb, hx, hy⟩ => by
      obtain ⟨hm, hunit⟩ := pt_unit (B i) (hi i) ha hb hx hy
      have hv := ((B i).valuation_eq_one_iff _).1 hunit
      show (a i + tf i * b i)⁻¹ ∈ B i
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
      simp only [tf]
      rw [hv, inv_one]
  refine ⟨⟨tf, ht⟩, isUnit_iff_exists_inv.2 ⟨⟨fun i => (a i + tf i * b i)⁻¹, hu⟩, ?_⟩⟩
  apply RestrictedProduct.ext
  intro i
  show (a i + tf i * b i) * (a i + tf i * b i)⁻¹ = 1
  exact mul_inv_cancel₀ (hne i)

theorem stable_rank_one_finite_adeles (F : Type) [Field F] [NumberField F] :
    Cj.HasStableRangeOne (FiniteAdeleRing (𝓞 F) F) :=
  stable_rank_one_restricted_product (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)

theorem stable_rank_one_infinite_adeles (F : Type) [Field F] [NumberField F] :
    Cj.HasStableRangeOne (InfiniteAdeleRing F) :=
  stable_rank_one_pi_field

theorem stable_rank_one_adeles : Cj.AdeleStableRankOne := by
  intro F _ _
  exact sr1_prod (stable_rank_one_infinite_adeles F) (stable_rank_one_finite_adeles F)

end PI.VolSemiDirect.W.SR
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LcscHAOf
section
noncomputable section

namespace PI.VolSemiDirect.W.Lc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem lcscHA_of (hT : TensTop) : LcscHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  obtain ⟨htr, ht2, hlc, hsc⟩ := hT F E
  have : Module.Finite F E := finite_nf F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hs : Continuous (sigR (AF F) σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (sigL (AF F) σ)
  have hcl : IsClosed ((HR (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
      Set (GL (Fin M) (AF F ⊗[F] E))) := by
    have hc : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
        Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) * JR (AF F) J *
          (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := by
      unfold Formalism.UG.cT
      have h0 : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
          (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := Units.continuous_val
      exact (((h0.matrix_map hs).matrix_transpose).matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  have hMlc : LocallyCompactSpace (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → AF F ⊗[F] E))
  have hMsc : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → AF F ⊗[F] E))
  have hMt2 : T2Space (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → AF F ⊗[F] E))
  have hMosc : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).symm.isEmbedding.secondCountableTopology
  have hGe := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
  have hGlc : LocallyCompactSpace (GL (Fin M) (AF F ⊗[F] E)) := hGe.locallyCompactSpace
  have hGsc : SecondCountableTopology (GL (Fin M) (AF F ⊗[F] E)) :=
    hGe.isEmbedding.secondCountableTopology
  have hGt2 : T2Space (GL (Fin M) (AF F ⊗[F] E)) := hGe.isEmbedding.t2Space
  have r : LCSC (HR (AF F) σ J) :=
    ⟨hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
      hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance,
      inferInstance⟩
  exact r

end PI.VolSemiDirect.W.Lc
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.StabilizerFixesFrameVector
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem stabilizer_fixes_frame_vector {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [S0, mem_stabT] at hg
  have := hg (Fin.castSucc a)
  simpa [F0, Fin.snoc_castSucc] using this

theorem stabilizer_fixes_frame_span {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P)
    (x : Fin M → R ⊗[F] E) (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J g x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, _, rfl⟩ := hy
    exact stabilizer_fixes_frame_vector R σ J P hg a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem norm_gen {r : ℕ} (P : Frame E M r) (h : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (n : HA R σ J) (hn : n ∈ FrameUnipotentSubgroup R σ J P) : h * n * h⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by
  have hHS := heisenberg_le_stabilizer R σ J P hh
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf] at hn ⊢
  have hS : h * n * h⁻¹ ∈ S0 R σ J P :=
    (S0 R σ J P).mul_mem ((S0 R σ J P).mul_mem hHS hn.2) ((S0 R σ J P).inv_mem hHS)
  refine ⟨?_, hS⟩
  have hnN := hn.1
  show UniC R σ J P.e (h * n * h⁻¹) ∧ ∀ v, InXperp R σ J P v →
    lin R σ J (h * n * h⁻¹) v - v ∈ spanR (F := F) R P.e Set.univ
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [stabilizer_fixes_frame_vector R σ J P hS b, sub_self]
    exact Submodule.zero_mem _
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      have e1 := stabilizer_fixes_frame_vector R σ J P ((S0 R σ J P).inv_mem hHS) a
      rw [← e1, hR_lin]
      exact hv a
    have hnu : lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v ∈ spanR (F := F) R P.e Set.univ :=
      hnN.2 _ hu
    have key : lin R σ J (h * n * h⁻¹) v - v =
        lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) := by
      rw [map_sub, lin_mul, lin_mul, lin_lin_inv]
    rw [key, stabilizer_fixes_frame_span R σ J P hHS _ hnu]
    exact hnu

end Gen

theorem normal_subgroup_holds : NormStep := by
  intro F E _ _ _ _ _ σ _ M J _ r P T _ _ h hh n hn
  exact norm_gen (AF F) σ J P h hh n hn

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.UniHaar
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory

def IsLowUni {A : Type} [CommRing A] {k : ℕ} (U : Matrix (Fin k) (Fin k) A) : Prop :=
  (∀ i, U i i = 1) ∧ ∀ i j : Fin k, i < j → U i j = 0

theorem mulVec_succAbove_step {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] {k : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + 1)) A) (p : Fin (k + 1)) (hpp : U p p = 1)
    (hp : ∀ i, U (p.succAbove i) p = 0)
    (hIH : MeasurePreserving (U.submatrix p.succAbove p.succAbove).mulVec
      (Measure.pi fun _ : Fin k => ν) (Measure.pi fun _ : Fin k => ν)) :
    MeasurePreserving U.mulVec (Measure.pi fun _ : Fin (k + 1) => ν)
      (Measure.pi fun _ : Fin (k + 1) => ν) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => A) p with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) p
  set U' := U.submatrix p.succAbove p.succAbove with hU'
  set r : (Fin k → A) → A := fun v => ∑ i, U p (p.succAbove i) * v i with hr
  have hrm : Measurable r :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hskew : MeasurePreserving (fun z : (Fin k → A) × A => (U'.mulVec z.1, r z.1 + z.2))
      ((Measure.pi fun _ : Fin k => ν).prod ν) ((Measure.pi fun _ : Fin k => ν).prod ν) :=
    hIH.skew_product (g := fun v a => r v + a) ((hrm.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun v => map_add_left_eq_self ν (r v))
  have hT : MeasurePreserving (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2))
      (ν.prod (Measure.pi fun _ : Fin k => ν)) (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap
  have hmul : U.mulVec = e.symm ∘ (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2)) ∘ e := by
    funext x
    apply e.injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    have hex : ∀ y : Fin (k + 1) → A, e y = (y p, fun i => y (p.succAbove i)) := fun y => rfl
    rw [hex, hex]
    refine Prod.ext ?_ ?_
    · show (∑ j, U p j * x j) = r (fun i => x (p.succAbove i)) + x p
      rw [Fin.sum_univ_succAbove _ p, hpp, one_mul, add_comm]
    · funext i
      show (∑ j, U (p.succAbove i) j * x j) = ∑ j, U' i j * x (p.succAbove j)
      rw [Fin.sum_univ_succAbove _ p, hp i, zero_mul, zero_add]
      rfl
  rw [hmul]
  exact (MeasurePreserving.symm e he_mp).comp (hT.comp he_mp)

theorem uni_measurePreserving {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] :
    ∀ (k : ℕ) (U : Matrix (Fin k) (Fin k) A), (IsLowUni U ∨ IsLowUni U.transpose) →
      MeasurePreserving U.mulVec (Measure.pi fun _ : Fin k => ν)
        (Measure.pi fun _ : Fin k => ν) := by
  intro k
  induction k with
  | zero =>
    intro U _
    have h0 : U.mulVec = id := by
      funext x i
      exact i.elim0
    rw [h0]
    exact MeasurePreserving.id _
  | succ k ih =>
    intro U hU
    rcases hU with hL | hT
    · refine mulVec_succAbove_step ν U (Fin.last k) (hL.1 _) (fun i => ?_)
        (ih _ (Or.inl ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_last i)
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.1 _
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)
    · refine mulVec_succAbove_step ν U 0 (hT.1 0) (fun i => ?_)
        (ih _ (Or.inr ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_zero]
        exact hT.2 0 i.succ (Fin.succ_pos i)
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.1 _
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.2 _ _ (Fin.succ_lt_succ_iff.mpr hab)

theorem uni_haar {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (k : ℕ) (U : Matrix (Fin k) (Fin k) A) (hU : IsLowUni U ∨ IsLowUni U.transpose)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map U.mulVec = μ := by
  have hpi : (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)),
    Measure.map_smul, (uni_measurePreserving (Measure.addHaar : Measure A) k U hU).map_eq]

theorem transvection_uni {A : Type} [CommRing A] {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : A) :
    IsLowUni (Matrix.transvection i j c) ∨ IsLowUni (Matrix.transvection i j c).transpose := by
  have key : ∀ a b : Fin k, (i = a ∧ j = b → False) → Matrix.single i j c a b = 0 := fun a b h => by
    rw [Matrix.single_apply, if_neg (fun hh => h hh)]
  have tac : ∀ a b : Fin k, (a < b ∧ i = a ∧ j = b → False) ∨ True := fun _ _ => Or.inr trivial
  rcases lt_or_gt_of_ne hij with h | h
  · right
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_gt hab), key b a (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]
  · left
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_lt hab), key a b (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]

theorem transvection_preserves_haar : TransvHaar := by
  intro A _ _ _ _ _ _ _ _ k i j hij c μ hμ
  haveI := hμ
  exact uni_haar k _ (transvection_uni i j hij c) μ

end PI.VolSemiDirect.W.Cj
end
end

