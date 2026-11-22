import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mem_span_range_of_isBaseChange {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (w : N) : w ∈ Submodule.span S (Set.range f) := by
  obtain ⟨y, rfl⟩ := hf.equiv.surjective w
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [hf.equiv_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem le_of_span_eq_top_of_isBaseChange {R S N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (P Q : Submodule R N) (hPQ : P ≤ Q) (hQ : IsBaseChange S Q.subtype)
    (hP : Submodule.span S (P : Set N) = ⊤) : Q ≤ P := by
  let ι := Submodule.inclusion hPQ
  have hs : Function.Surjective (ι.lTensor S) := by
    intro y
    have hv : hQ.equiv y ∈ Submodule.span S (P : Set N) := hP ▸ Submodule.mem_top
    have key : ∀ v ∈ Submodule.span S (P : Set N), ∃ y' : S ⊗[R] P, hQ.equiv (ι.baseChange S y') = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp [ι, hQ.equiv_tmul]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simp [ha]⟩
    obtain ⟨y', hy'⟩ := key _ hv
    exact ⟨y', by rw [← LinearMap.baseChange_eq_ltensor]; exact hQ.equiv.injective hy'⟩
  have hι := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).mp hs
  intro x hx
  obtain ⟨y, hy⟩ := hι ⟨x, hx⟩
  have hx' : (y : N) = x := congrArg Subtype.val hy
  exact hx' ▸ y.2

theorem lift_solution_succ_of_descent {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C)
    (p q : Hom C D) (hcomm : p.comp h = q.comp h) (m : ℕ) (hff : (qmap h m).FaithfullyFlat)
    (ε : Matrix (Fin d) (Fin d) D.A)
    (H : ∀ k : ℕ, letI := (qmap h k).toAlgebra
      ∃ N : Submodule (B.A ⧸ adI B ^ k) (Fin d → C.A ⧸ adI C ^ k),
        (∀ z, z ∈ N ↔ (fun i => qmap p k (z i)) =
          (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec fun i => qmap q k (z i)) ∧
        IsBaseChange (C.A ⧸ adI C ^ k) N.subtype)
    (z : Fin d → C.A) (hz : ∀ i, p.f (z i) - ε.mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧
      ∀ i, p.f (z' i) - ε.mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  have hmem : ∀ (k : ℕ) (w : Fin d → C.A),
      ((fun i => qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i))) =
        (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i)))) ↔
      ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ k := by
    intro k w
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have e1 : qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i)) = Ideal.Quotient.mk (adI D ^ k) (p.f (w i)) :=
      qmap_mk p k _
    have e2 : (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec
        (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i))) i =
        Ideal.Quotient.mk (adI D ^ k) (ε.mulVec (fun j => q.f (w j)) i) := by
      simp only [qmap_mk]
      exact (RingHom.map_mulVec (Ideal.Quotient.mk (adI D ^ k)) ε (fun j => q.f (w j)) i).symm
    rw [e1, e2]
    exact Ideal.Quotient.eq
  letI alg0 : Algebra (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := (qmap h m).toAlgebra
  letI alg1 : Algebra (B.A ⧸ adI B ^ (m + 1)) (C.A ⧸ adI C ^ (m + 1)) := (qmap h (m + 1)).toAlgebra
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := hff
  obtain ⟨N, hN, hbN⟩ := H m
  obtain ⟨N', hN', hbN'⟩ := H (m + 1)
  have hpq : ∀ b : B.A, p.f (h.f b) = q.f (h.f b) := fun b => congrArg (fun g : Hom B D => g.f b) hcomm
  let P : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m) :=
    { carrier := {x | ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = x ∧
        ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ (m + 1)}
      zero_mem' := ⟨0, by funext i; simp, fun i => by
        have e : (fun j => q.f ((0 : Fin d → C.A) j)) = 0 := funext fun j => by simp
        rw [e, Matrix.mulVec_zero]
        simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        refine ⟨w₁ + w₂, by funext i; simp, fun i => ?_⟩
        have := Ideal.add_mem _ (h₁ i) (h₂ i)
        convert this using 1
        have e : (fun j => q.f ((w₁ + w₂) j)) = (fun j => q.f (w₁ j)) + (fun j => q.f (w₂ j)) := by
          funext j; simp
        rw [e, Matrix.mulVec_add]
        simp only [Pi.add_apply, map_add]
        ring
      smul_mem' := by
        rintro c _ ⟨w, rfl, hw⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        refine ⟨fun i => h.f b * w i, ?_, fun i => ?_⟩
        · funext i
          simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qmap_mk]
        · have := Ideal.mul_mem_left _ (q.f (h.f b)) (hw i)
          convert this using 1
          have e : (fun j => q.f (h.f b * w j)) = q.f (h.f b) • (fun j => q.f (w j)) := by
            funext j; simp
          rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hpq, mul_sub] }
  have hPN : P ≤ N := by
    rintro _ ⟨w, rfl, hw⟩
    exact (hN _).2 ((hmem m w).2 fun i => Ideal.pow_le_pow_right (Nat.le_succ m) (hw i))
  have hspan : Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    let πC := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m) : adI C ^ (m + 1) ≤ adI C ^ m)
    let r : (Fin d → C.A ⧸ adI C ^ (m + 1)) → (Fin d → C.A ⧸ adI C ^ m) := fun y i => πC (y i)
    have hr : ∀ y ∈ Submodule.span (C.A ⧸ adI C ^ (m + 1)) (Set.range N'.subtype),
        r y ∈ Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨x, hxN⟩, rfl⟩ := hx
        apply Submodule.subset_span
        obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk _ (w i)) = x :=
          ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
            funext fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
        exact ⟨w, by funext i; simp [r, πC], (hmem (m + 1) w).1 ((hN' _).1 hxN)⟩
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i; simp [r]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext i; simp [r]
      | smul c x _ hx =>
        convert Submodule.smul_mem _ (πC c) hx using 1
        funext i; simp [r]
    obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    have := hr (fun i => Ideal.Quotient.mk _ (w i)) (mem_span_range_of_isBaseChange hbN' _)
    convert this using 1
    funext i; simp [r, πC]
  have hNP : N ≤ P := le_of_span_eq_top_of_isBaseChange P N hPN hbN hspan
  have hzN : (fun i => Ideal.Quotient.mk (adI C ^ m) (z i)) ∈ N := (hN _).2 ((hmem m z).2 hz)
  obtain ⟨w, hw, hwE⟩ := hNP hzN
  exact ⟨w, fun i => Ideal.Quotient.eq.1 (congrFun hw i), hwE⟩

theorem lift_solution_succ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  intro l _ K bk d S B C D h f p q hcov hpo m z hz
  refine lift_solution_succ_of_descent h p q hpo.comm m (hcov.ff m) _ (fun k => ?_) z hz
  exact (GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p q hcov hpo k).imp fun N hN => ⟨hN.1, hN.2.2.2⟩

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtale
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LimBasis

variable {l : ℕ} [hl : Fact l.Prime]

theorem sep (z : WCb l) (h : ∀ n, (l : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

def Cg {ι κ : Type} (n : ℕ) (M : Matrix ι κ (WCb l)) : Prop := ∃ Y : Matrix ι κ (WCb l), M = ((l : WCb l) ^ n) • Y

section Cg

variable {ι κ μ : Type} {n : ℕ}

theorem cg_of {M : Matrix ι κ (WCb l)} (h : ∀ i j, (l : WCb l) ^ n ∣ M i j) : Cg n M :=
  ⟨Matrix.of fun i j => Classical.choose (h i j), by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Classical.choose_spec (h i j)⟩

theorem Cg.dvd {M : Matrix ι κ (WCb l)} (h : Cg n M) (i : ι) (j : κ) : (l : WCb l) ^ n ∣ M i j := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y i j, by simp⟩

theorem Cg.add {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M + M') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y + Y', (smul_add _ _ _).symm⟩

theorem Cg.neg {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (-M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨-Y, (smul_neg _ _).symm⟩

theorem Cg.sub {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M - M') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem Cg.mul_left [Fintype κ] {M : Matrix κ μ (WCb l)} (P : Matrix ι κ (WCb l)) (h : Cg n M) : Cg n (P * M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨P * Y, Matrix.mul_smul _ _ _⟩

theorem Cg.mul_right [Fintype κ] {M : Matrix ι κ (WCb l)} (P : Matrix κ μ (WCb l)) (h : Cg n M) : Cg n (M * P) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y * P, Matrix.smul_mul _ _ _⟩

theorem Cg.map (f : WCb l →+* WCb l) {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (M.map f) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y.map f, Matrix.ext fun i j => by simp⟩

theorem Cg.eq_zero {M : Matrix ι κ (WCb l)} (h : ∀ n, Cg n M) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  exact sep _ fun n => (h n).dvd i j

end Cg

variable {K : FinExt l} (bk : BK K)

def InOE {ι κ : Type} (M : Matrix ι κ (WCb l)) : Prop := ∀ i j, M i j ∈ bk.OE

variable {bk}

theorem InOE.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ (WCb l)} {M' : Matrix κ μ (WCb l)} (h : InOE bk M)
    (h' : InOE bk M') : InOE bk (M * M') := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h i k) (h' k j)

theorem InOE.smul {ι κ : Type} {c : WCb l} (hc : c ∈ bk.OE) {M : Matrix ι κ (WCb l)} (h : InOE bk M) :
    InOE bk (c • M) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (h i j)

variable (bk)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem inOE_evW {ι κ : Type} (M : Matrix ι κ bk.S) : InOE bk (M.map bk.evW) := fun i j => evW_mem bk (M i j)

theorem mem_of_approx {x : WCb l} (h : ∀ n, ∃ w ∈ bk.OE, (l : WCb l) ^ n ∣ x - w) : x ∈ bk.OE := by
  intro n
  obtain ⟨w, hw, c, hc⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hw n
  exact ⟨m, s, y + bk.evW X ^ m * c, by linear_combination bk.evW X ^ m * hc + hy⟩

theorem inOE_of_approx {ι κ : Type} {A : Matrix ι κ (WCb l)}
    (h : ∀ n, ∃ M : Matrix ι κ (WCb l), InOE bk M ∧ Cg n (A - M)) : InOE bk A := fun i j =>
  mem_of_approx bk fun n => by
    obtain ⟨M, hM, hc⟩ := h n
    exact ⟨M i j, hM i j, by simpa [Matrix.sub_apply] using hc.dvd i j⟩

theorem E_not_dvd : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨s, hs⟩
  have h := congrArg (PowerSeries.coeff bk.Ep.natDegree) hs
  rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 : (1 : Wq l bk.a) = (PowerSeries.coeff bk.Ep.natDegree s) * (l : Wq l bk.a) := by
    rw [h, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  have h3 := congrArg (fun w : Wq l bk.a => w.coeff 0) h2
  simp only [WittVector.one_coeff_zero, WittVector.mul_charP_coeff_zero] at h3
  exact one_ne_zero h3

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  intro l _ K bk τ _ d N ρ tw F T0 hT0 hR
  obtain ⟨-, -, hunit, -, -, hfix, hfrob⟩ := GlobalTheory.OEDvr.main l K bk
  obtain ⟨e, he, heE⟩ := hunit bk.E (E_not_dvd bk)
  have key : ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)),
      InOE bk R ∧ InOE bk R' ∧ Cg n (zW (tw.Pi n) * (F n).T - T0 * R) ∧
      Cg n (T0 - zW (tw.Pi n) * (F n).T * R') := fun n => by
    obtain ⟨R, R', h1, h2, h3, h4⟩ := hR n
    refine ⟨R, R', h1, h2, cg_of h3, ?_⟩
    have e1 : T0 - zW (tw.Pi n) * (F n).T * R' =
        -(T0 * (R * R' - 1)) - (zW (tw.Pi n) * (F n).T - T0 * R) * R' := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e1]
    exact ((cg_of h4).mul_left T0).neg.sub ((cg_of h3).mul_right R')
  have hdet : IsUnit T0.det := (Matrix.isUnit_iff_isUnit_det T0).1 hT0
  refine ⟨fun g hg => ?_, ?_⟩
  · let σ : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hσz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map σ = zW M := fun M =>
      Matrix.ext fun i j => (galW l (g : GQ l)).commutes (M i j)
    change zW (ρ g).val * T0.map σ = T0
    refine sub_eq_zero.1 (Cg.eq_zero fun n => ?_)
    obtain ⟨R, R', -, hR', -, h2⟩ := key n
    have hR'σ : R'.map σ = R' := Matrix.ext fun i j => hfix g hg _ (hR' i j)
    have hT' : zW (tw.ρ' n g).val * (F n).T.map σ = (F n).T := (F n).fix g hg
    have hequi : Cg n (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) := by
      have e2 : zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val =
          -zW (tw.Pi n * (tw.ρ' n g).val - (ρ g).val * tw.Pi n) := by
        simp only [zW, Matrix.map_sub _ (map_sub (algebraMap ℤ_[l] (WCb l))), Matrix.map_mul, neg_sub]
      rw [e2]
      refine (cg_of fun i j => ?_).neg
      have := map_dvd (algebraMap ℤ_[l] (WCb l)) ((tw.onto n).equi g i j)
      rwa [map_pow, map_natCast] at this
    have h3 : Cg n (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') := by
      have := h2.map σ
      rwa [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz, hR'σ] at this
    have e3 : zW (ρ g).val * T0.map σ - T0 = zW (ρ g).val * (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') +
        (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) * (F n).T.map σ * R' -
        (T0 - zW (tw.Pi n) * (zW (tw.ρ' n g).val * (F n).T.map σ) * R') := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [e3, hT']
    exact ((h3.mul_left _).add ((hequi.mul_right _).mul_right _)).sub h2
  · let f : WCb l →+* WCb l := (frobW l).toRingHom
    change ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧
      T0.map f = T0 * A0 ∧ A0 * A0' = 1
    have hfz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map f = zW M := fun M =>
      Matrix.ext fun i j => (frobW l).commutes (M i j)
    have hfOE : ∀ {m m' : Type} {M : Matrix m m' (WCb l)}, InOE bk M → InOE bk (M.map f) :=
      fun h i j => hfrob _ (h i j)
    have hTf : IsUnit (T0.map f) := hT0.map f.mapMatrix
    have hdetf : IsUnit (T0.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hTf
    have heN : bk.evW bk.E ^ N * e ^ N = 1 := by rw [← mul_pow, heE, one_pow]
    have hφ : ∀ n, (F n).T.map f = (F n).T * (e ^ N • (F n).A.map bk.evW) := fun n => by
      have h := (F n).φ
      rw [Matrix.mul_smul, ← h, smul_smul, mul_comm (e ^ N), heN, one_smul]
      rfl
    have hφ' : ∀ n, (F n).T = (F n).T.map f * (e ^ N • (F n).A'.map bk.evW) := fun n => by
      have hA : (F n).A.map bk.evW * (F n).A'.map bk.evW =
          (bk.evW bk.E ^ (2 * N)) • (1 : Matrix (Fin (tw.d' n)) (Fin (tw.d' n)) (WCb l)) := by
        rw [← Matrix.map_mul, (F n).A_mul]
        refine Matrix.ext fun i j => ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hs : e ^ N * (e ^ N * bk.evW bk.E ^ (2 * N)) = 1 := by
        linear_combination (bk.evW bk.E ^ N * e ^ N + 1) * heN
      rw [hφ n, Matrix.mul_assoc]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, Matrix.mul_one]
      rw [hs, one_smul]
    refine ⟨T0⁻¹ * T0.map f, (T0.map f)⁻¹ * T0, ?_, ?_, ?_, ?_⟩
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R * (e ^ N • (F n).A.map bk.evW) * R'.map f,
        (hR.mul ((inOE_evW bk _).smul (pow_mem he N))).mul (hfOE hR'), ?_⟩
      have i4 : T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f) =
          (T0 - zW (tw.Pi n) * (F n).T * R').map f +
            (zW (tw.Pi n) * (F n).T - T0 * R) * (e ^ N • (F n).A.map bk.evW) * R'.map f := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz, hφ n]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
      have e4 : T0⁻¹ * T0.map f - R * (e ^ N • (F n).A.map bk.evW) * R'.map f =
          T0⁻¹ * (T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f)) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
      rw [e4, i4]
      exact ((h2.map f).add ((h1.mul_right _).mul_right _)).mul_left _
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R.map f * (e ^ N • (F n).A'.map bk.evW) * R',
        ((hfOE hR).mul ((inOE_evW bk _).smul (pow_mem he N))).mul hR', ?_⟩
      have e6 : zW (tw.Pi n) * ((F n).T.map f * ((e ^ N • (F n).A'.map bk.evW) * R')) =
          zW (tw.Pi n) * ((F n).T * R') := by
        rw [← Matrix.mul_assoc ((F n).T.map f), ← hφ' n]
      have i5 : T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R') =
          (T0 - zW (tw.Pi n) * (F n).T * R') +
            (zW (tw.Pi n) * (F n).T - T0 * R).map f * (e ^ N • (F n).A'.map bk.evW) * R' := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz]
        simp only [Matrix.sub_mul, Matrix.mul_assoc, e6]; abel
      have e5 : (T0.map f)⁻¹ * T0 - R.map f * (e ^ N • (F n).A'.map bk.evW) * R' =
          (T0.map f)⁻¹ * (T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R')) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdetf]
      rw [e5, i5]
      exact (h2.add (((h1.map f).mul_right _).mul_right _)).mul_left _
    · exact (Matrix.mul_nonsing_inv_cancel_left T0 _ hdet).symm
    · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdetf, Matrix.nonsing_inv_mul _ hdet]

end GlobalTheory.LimBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProof
section
noncomputable section

namespace GlobalTheory.Pass.LocDirect

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : StepLocDirect := by
  intro D hLOC hBK hFont hPDR i r hr Xs w hw hdeg n e hPot hLift k M hSub
  have hM : Continuous fun g => M g := hSub.1
  have hc : ∀ x, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r x) g := fun x =>
    GlobalTheory.PotDual.continuous_loc D i w hw _ (FamCont.stepCont D i r hr x).1
  unfold LocBoundP
  have hcut : cutCoc i w hw r Xs M = ⋃₀ {A | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs)
      (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      A = LocDirect.pushSet i w hw r M x E Y hst hE} := by
    ext c
    rw [LocDirect.mem_cutCoc, Set.mem_sUnion]
    constructor
    · rintro ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
      exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
    · rintro ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
      exact ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
  rw [hcut]
  apply GlobalTheory.T.lenMod_span_sUnion_le_of_directed'
  · rintro _ ⟨a₁, x₁, hx₁, E₁, Y₁, hY₁, hst₁, hE₁, rfl⟩ _ ⟨a₂, x₂, hx₂, E₂, Y₂, hY₂, hst₂, hE₂, rfl⟩
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, h1, h2⟩ :=
      GlobalTheory.T.exists_merged_module_pushouts_contain_both D i w hw r Xs M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
    exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, h1, h2⟩
  · rintro _ ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩
    let U := LocDirect.ModuleGaloisRepresentation i w hw M hM
    let X := LocDirect.Xgrep i w hw r x (fun j => hc (x j)) Y hst
    obtain ⟨K', hK', hcrys⟩ := GlobalTheory.T.tensorLocalField_isCrystalline_over_familyField D hFont i r hr Xs w hw n hPot M hSub hM
    have hUdR : IsDR (Br.PD D.loc D.nbr i w hw) U.ρ :=
      hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK' U hcrys
    obtain ⟨U', LT', PU, hdual, hrank⟩ := GlobalTheory.T.crystalline_over_extension D hFont hBK hPDR i w hw hdeg M hM K' hK' hcrys
    obtain ⟨X', PX, hX⟩ := GlobalTheory.T.exists_tateDual_localGaloisRep_atPlace D i w hw X
    have hLA := GlobalTheory.T.liftAll_of_blochKatoLiftingFamilyAtPlace D i w hw r hr Xs e hLift M hSub hM a x hx (fun j => hc (x j)) Y hst
    have hsub := GlobalTheory.T.pushouts_mem_span_localSelmerPushouts D hFont i r hr Xs w hw n hPot M hM a x hx (fun j => hc (x j)) E Y hY hst hE
    obtain ⟨m, k', hm, hk', hle⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
      (goodO_ringOfIntegers _ _) X X U X' U' 1 PX PU (Br.locLat D.nbr i w hw M) LT' e
      ⟨⟨LinearEquiv.refl _ _, fun g v => by simp⟩, hUdR, hX, hdual, Or.inl hLA⟩
    have hmono := GlobalTheory.T.lenMod_mono_left' _ _ (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M))
      (Submodule.span_le.2 hsub)
    have hT : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
      have hinj := stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k
      show finrank _ ↥(stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k) = k
      exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm.trans (Module.finrank_fin_fun _)
    have h2 : m ≤ 2 * k * e * k' := by
      refine hle.trans ?_
      calc _ ≤ e * (k + k) * k' := by
            gcongr
            · exact hrank
            · exact hT.le
        _ = 2 * k * e * k' := by ring
    calc _ ≤ BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X U (Br.locLat D.nbr i w hw M))
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) := hmono
      _ = (m : ℕ∞) := hm
      _ ≤ ((2 * k * e * k' : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = _ := by
        rw [show lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = (k' : ℕ∞) from hk']
        push_cast; ring

end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_theta_kernel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ ω : AK K, ω ≠ 0 → thetaK K ω = 0 → frobq K ω = inO K π * ω + ω ^ resCard K →
      (∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n) →
      ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  first | exact @GlobalTheory.LTPeriodKerSq.main | exact GlobalTheory.LTPeriodKerSq.main | (intros; apply GlobalTheory.LTPeriodKerSq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGamma
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CocycleInj

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  intro D HW F l _ K s LL h W E T hT M m hy hz
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius D HW F l K s LL h T hT M m hy
  exact GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma D HW F l K s LL h T hT M a m hy hz ha

end GlobalTheory.NL.CocycleInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  first | exact @GlobalTheory.BKGal.muPow_smul_actB_sub_mem | exact GlobalTheory.BKGal.muPow_smul_actB_sub_mem | (intros; apply GlobalTheory.BKGal.muPow_smul_actB_sub_mem <;> assumption)
end

