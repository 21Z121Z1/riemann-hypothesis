import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver secOver secMOver)

noncomputable section

section OneBlock

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

def unitSigmaEquiv (κ : Type) : (Σ _ : Unit, κ) ≃ κ where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {κ : Type} [Fintype κ]

omit [Fintype κ] in

theorem chartRingOver_oneBlock_eq (x : κ → Ω) (c : Unit → κ) :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin F (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

omit [Fintype κ] in

theorem mem_secOver_oneBlock (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin F (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())

omit [Fintype κ] in

theorem secOver_oneBlock_comp {κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'

omit [Fintype κ] in

theorem relDim_oneBlock_eq_iff (P : Ideal (MvPolynomial (Σ _ : Unit, κ) F)) (e : ℕ) :
    FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MvPolynomial (Σ _ : Unit, κ) F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit]

end OneBlock

section FirstTyping

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}

theorem twistSys_secs_eq_secOver (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys F x n).secs = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_oneBlock]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  change t ∈ Kleiman.twistMod F x n (Kleiman.singleChart hj) ↔ _
  rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
  have hA : Kleiman.chartRing F x (Kleiman.singleChart hj) =
      Algebra.adjoin F (Set.range fun i => x i / x j) :=
    (chartRingOver_oneBlock x (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
  rw [← hA]
  have hxn : x j ^ n ≠ 0 := zpow_ne_zero n hj
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ hxn, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ hxn t

theorem mIdealOver_oneBlock (x : Fin (N + 1) → Ω) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = Kleiman.primeOfOne (S := F) x := by
  have hc : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars F).comp
      (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = (Kleiman.cone (S := F) x).comp (Kleiman.oneBlock (S := F) (N := N)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, Kleiman.oneBlock, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  ext f
  rw [mIdealOver, RingHom.mem_ker, Kleiman.primeOfOne, Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  have h := congrArg (fun φ => φ f) hc
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective).symm

theorem isSubvar_primeOf_iff (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) x) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hX : ∀ i, (X i : Kleiman.Poly F N) ∈ Kleiman.primeOf (S := F) x ↔ x i = 0 := fun i => by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X F i), aeval_X]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.relevant
    exact ⟨⟨i, fun hx => hi ((hX i).mpr hx)⟩, h.dim⟩
  · rintro ⟨⟨i, hi⟩, hdim⟩
    exact ⟨inferInstance, fun p hp d => Kleiman.homogeneousComponent_mem_primeOf x hp d, le_rfl,
      ⟨i, fun h => hi ((hX i).mp h)⟩, hdim⟩

theorem isSubvar_iff_relDim (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ FieldNumbers.relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  rw [isSubvar_primeOf_iff, relDim_oneBlock_eq_iff, mIdealOver_oneBlock, HilbertPositive.ringKrullDim_primeOfOne]

end FirstTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem SectionCount.bound_from_one {X : ℝ} {d : ℕ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  refine ⟨max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)), fun n hn => ?_⟩
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rcases le_or_gt n₀ n with h | h
  · have h1 := hn₀ n h
    have h2 : C * (n : ℝ) ^ d ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (n : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hX : X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
        |X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc X * (n : ℝ) ^ (d + 1) ≤ |X| * (n : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self X) (by positivity)
        _ ≤ |X| * (n₀ : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) _)
              (abs_nonneg X)
    have hM := le_max_right C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))
    have hM0 : 0 ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) :=
      le_trans (by positivity) hM
    have h3 := le_mul_of_one_le_right hM0 hnd
    linarith [hf n]

theorem SectionCount.exists_ne_zero_of_isSubvar {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {e : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := k) x) e) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  rw [Kleiman.primeOf, ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal, RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem SectionCount.transfer (hBase : BaseRealises.Statement)
    (hP : PowRealises.Statement) (hN : NumModel.Statement)
    (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω) (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (Q : Kleiman.LineBundle F x) (ν : K → ℤ)
    (hQ : BundleRealises y k₀ Q ν) (d q : ℕ) (hsub : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) (d + 1)) :
    ((Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) -
        ((d + 1 : ℕ) : ℤ) * Kleiman.interNum (Kleiman.primeOf (S := F) x)
          (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
            (fun _ : Fin d => Q.toSubSystem)) : ℤ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
        ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F y)
          (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℝ) ∧
    ∀ n : ℕ, (Kleiman.twistMul Q.toSubSystem n (-((n : ℤ) * q))).secs =
      secOver F y (n • (ν - q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
  have h1 : Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) =
      NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) :=
    hN F K ι Ω y k₀ N e x hx hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  have hqs : ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    funext j; simp
  have hL : (fun i => (Fin.cons (α := fun _ => Kleiman.LineBundle F x) (Kleiman.twistBundle F x (q : ℤ))
      (fun _ : Fin d => Q) i).toSubSystem) =
      Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have h2 : Kleiman.interNum (Kleiman.primeOf (S := F) x)
      (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem)) =
      NumbersDVR.intNum F (mIdealOver F y)
        (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
    rw [NumbersDVR.VerticalDivisorsCommuting.intNum_snoc, ← hL, ← hqs]
    exact hN F K ι Ω y k₀ N e x hx hmod (d + 1) _ (Fin.cons ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) fun _ => ν)
      (fun i => Fin.cases (hBase F K ι Ω y k₀ N e x hx hmod (q : ℤ)) (fun _ => hQ) i) hsub
  refine ⟨by rw [h1, h2]; push_cast; ring, fun n => ?_⟩
  rw [hP F K ι Ω y k₀ N e x hx hmod Q ν hQ n (-((n : ℤ) * q))]
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem SectionCount.equiv (hG : GraphModel.Statement) (hB : BundleOfDeg.Statement) (hD : ModelDim.Statement)
    (hBase : BaseRealises.Statement) (hP : PowRealises.Statement) (hV : VeryAmpleModel.Statement)
    (hN : NumModel.Statement) :
    Kleiman.SectionCount.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := by
  constructor
  · intro hA F _ K _ _ ι _ Ω _ _ y k₀ d ν q hmod hdim hva hq
    have hpos : 0 < Fintype.card (ι k₀) := by
      obtain ⟨i, -⟩ := hmod.1 k₀
      exact Fintype.card_pos_iff.2 ⟨i⟩
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
    obtain ⟨Q, hQ⟩ := hB F K ι Ω y k₀ N e hmod ν
    have hsub := (hD F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
    have hvaQ := (hV F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN F K ι Ω y k₀ N e _ rfl hmod Q ν hQ d q hsub
    obtain ⟨C, hC⟩ := hA F Ω N _ d Q q hsub hvaQ hq
    refine SectionCount.bound_from_one (fun n => Nat.cast_nonneg _) ⟨C, hC.mono fun n hn => ?_⟩
    rw [← hZ, ← hS n]
    exact hn
  · intro hB' k _ Ω _ _ N x d Nb b hsub hva hb
    obtain ⟨r, h, hby⟩ := hva
    have hgen : IsGraphGen Nb 0 h := fun I => by
      rw [Kleiman.SubSystem.twist_twistSys_zero]
      exact hby.generates I
    have hmod := hG k N Ω x Nb 0 (r + 1) h (SectionCount.exists_ne_zero_of_isSubvar hsub) hgen
    have hQ := realises_graph Nb 0 h hgen
    have hdim := (hD k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod (d + 1)).1 hsub
    have hvaB := (hV k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod Nb (graphDeg 0) hQ).1 ⟨r, h, hby⟩
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω
      (graphVec x h) baseBlock N (Equiv.refl _) x rfl hmod Nb (graphDeg 0) hQ d b hsub
    obtain ⟨C, hC⟩ := hB' k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock d (graphDeg 0) b
      hmod hdim hvaB hb
    refine ⟨C, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    rw [hZ, hS n]
    exact hC n hn

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FinrankSectionsOverEqH0
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc cechZc cechBc quotPart GlobalSectionsComparisonStatement)

noncomputable section

theorem altSum_eq_of_vanish (f : ℕ → ℕ) (B : ℕ) (h : ∀ i, 1 ≤ i → f i = 0) :
    ∑ i ∈ Finset.range (B + 1), (-1 : ℚ) ^ i * (f i : ℚ) = f 0 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by rw [h (i + 1) (by omega)]; simp]
  simp

theorem finrank_sectionsOver_eq_H0 (hB : GlobalSectionsComparisonStatement) {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K]
    {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (n : K → ℤ) :
    Module.finrank F (secOver F y n) = Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) n 0) := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB F K ι Ω y n hy
  let e1 : ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) ≃ₗ[F] secOver F y n :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hbot : (cechBc ι (quotPart F (mIdealOver F y)) n 0).comap
      (cechZc ι (quotPart F (mIdealOver F y)) n 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  let e2 : cechHc ι (quotPart F (mIdealOver F y)) n 0 ≃ₗ[F] ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) :=
    Submodule.quotEquivOfEqBot _ hbot
  rw [← e1.finrank_eq, e2.finrank_eq]

theorem SectionsPoly.proof (hB : GlobalSectionsComparisonStatement) (hE : EulerPoly.Statement) (hM : MultiSerre.Statement)
    (hR : RayVanish.Statement) : SectionsPoly.Statement := by
  intro F _ K _ dK ι _ Ω _ _ y k₀ hmod
  let lo : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain rfl : dK = @LinearOrder.toDecidableEq K lo := Subsingleton.elim _ _
  have hV : NumbersDVR.IsMultiHomogIdeal (mIdealOver F y) := isMultiHomogIdeal_mIdealOver y
  obtain ⟨B, χ, -, -, hχ⟩ := hE F K ι (mIdealOver F y) hV
  have key : ∀ m : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) m i)) →
      (Module.finrank F (secOver F y m) : ℚ) = eval (fun k => (m k : ℚ)) χ := by
    intro m hm
    rw [← hχ m, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    refine (altSum_eq_of_vanish (fun i => Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) m i)) B
      fun i hi => ?_).symm
    have := hm i hi
    exact Module.finrank_zero_of_subsingleton
  refine ⟨χ, ?_, fun β => ?_⟩
  · filter_upwards [hM F K ι (mIdealOver F y) hV] with m hm
    rw [← hm.2, ← key m hm.1, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    push_cast
    rfl
  · filter_upwards [hR F K ι Ω y k₀ hmod β] with c hc
    exact key _ hc

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelRowExact.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      CellAugExact F y (fun I => cellSec F y γ (baseCell k₀ e J.1 I))
        (Submodule.span F (chartSecOver F y k₀ e γ J))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelGenerated.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DoubleCech.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (N : ℕ)
    (x : Fin (N + 1) → Ω) (T : Kleiman.SubSystem F x Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ j, x j ≠ 0) →
    (∀ I, ¬ CellMeets y I → B I = ⊥) →
    (∀ J I, ¬ CellMeets y I → M J I = ⊥) →
    (∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) →
    (∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I)) →
    (∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) →
    ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellHOf F y B n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def RatioDim.Statement : Prop :=
  ∀ (k : Type) [Field k] (N m : ℕ) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)), W.IsPrime →
    NumbersDVR.IsMultiHomogIdeal W → ∀ j : Fin m,
      (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
      (∀ b : Fin m, ∃ f g : Kleiman.Poly k N,
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W) →
      ringKrullDim (NumbersDVR.MRing (graphIdx N m) k ⧸ W) =
        ringKrullDim (Kleiman.Poly k N ⧸ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) + 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def PullSecsModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₀ : Type) [Fintype K₀] [DecidableEq K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι₀ k) → Ω) (k₀ : K₀)
    (N N' : ℕ) (e : ι₀ k₀ ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω),
    x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y₀ k₀ ∘ e.symm → IsNoetherianRing S → (∀ k, ∃ i, y₁ ⟨k, i⟩ ≠ 0) → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀ →
    IndefiniteRowSideFullHecke.Kleiman2.Dominates S y₁ y₀ → IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') →
    ∀ (Q : Kleiman.LineBundle S x) (β : K₀ → ℤ),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys S x c)).secs =
        secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      Kleiman.pullSecs x' Q.toSubSystem = secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowChartAct.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)) (r a : Ω),
    r ∈ Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J →
    a ∈ cellSec S y γ (baseCell k₀ e J.1 I) → r * a ∈ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)),
    (∀ k, (I k).Nonempty) → CellMeets y I →
      chartSecOver S y k₀ e γ J ⊆ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSecGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (a : Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → a ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) →
      a ∈ chartSecOver S y k₀ e γ J

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

