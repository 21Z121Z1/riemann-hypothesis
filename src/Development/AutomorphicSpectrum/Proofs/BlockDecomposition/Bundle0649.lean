import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula

theorem relIndex_split {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (A B : AddSubgroup G) (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * A.relIndex (B ⊓ f.ker) := by
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ f.ker).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have h2 : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.mp hx
      obtain ⟨a, ha, k, hk, rfl⟩ := AddSubgroup.mem_sup.mp hx1
      refine AddSubgroup.mem_sup.mpr ⟨a, ha, k, AddSubgroup.mem_inf.mpr ⟨?_, hk⟩, rfl⟩
      have := B.sub_mem hx2 (hAB ha)
      simpa using this
    · refine sup_le (le_inf le_sup_left hAB) (le_inf ?_ inf_le_left)
      exact inf_le_right.trans le_sup_right
  have h3 : A.relIndex (A ⊔ (B ⊓ f.ker)) = A.relIndex (B ⊓ f.ker) :=
    AddSubgroup.relIndex_sup_left _ _
  have h4 := AddSubgroup.relIndex_mul_relIndex A ((A ⊔ f.ker) ⊓ B) B
    (le_inf le_sup_left hAB) inf_le_right
  rw [AddSubgroup.inf_relIndex_right, h2, h3] at h4
  rw [h1, ← h4, mul_comm]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_castSucc_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a b : Fin m) :
    blk σ c u d a.castSucc b.castSucc = c a b := by
  simp [blk]

theorem blk_castSucc_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a : Fin m) :
    blk σ c u d a.castSucc (Fin.last m) = u a := by
  simp [blk]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin (m + 1) → E) (i : Fin m) :
    (blk σ c u d).mulVec y i.castSucc
      = c.mulVec (fun j => y j.castSucc) i + y (Fin.last m) * u i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk_castSucc_castSucc,
    blk_castSucc_last]
  ring

variable [NumberField E]

def proj (E : Type) [Field E] [NumberField E] (m : ℕ) :
    (Fin (m + 1) → E) →ₗ[𝓞 E] (Fin m → E) :=
  LinearMap.funLeft (𝓞 E) E Fin.castSucc

@[simp] theorem proj_apply (m : ℕ) (v : Fin (m + 1) → E) (i : Fin m) :
    proj E m v i = v i.castSucc := rfl

theorem snoc_mem_intVec {m : ℕ} {y : Fin m → E} (hy : y ∈ intVec E m) (o : 𝓞 E) :
    (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E o) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨o, by simp⟩
  · obtain ⟨p, hp⟩ := hy j
    exact ⟨p, by simp [hp]⟩

theorem proj_mem_intVec {m : ℕ} {y : Fin (m + 1) → E} (hy : y ∈ intVec E (m + 1)) :
    proj E m y ∈ intVec E m := fun i => hy i.castSucc

theorem map_proj_intVec (m : ℕ) : (intVec E (m + 1)).map (proj E m) = intVec E m := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact proj_mem_intVec hy
  · intro y hy
    refine ⟨_, snoc_mem_intVec hy 0, ?_⟩
    funext i
    simp

theorem intVec_le_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : intVec E m ≤ lam c := le_sup_left

theorem mulVec_mem_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) {y : Fin m → E}
    (hy : y ∈ intVec E m) : c.mulVec y ∈ lam c :=
  Submodule.mem_sup_right ⟨y, hy, rfl⟩

theorem map_proj_lam {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) :
    (lam (blk σ c u d)).map (proj E m) = lam c ⊔ Submodule.span (𝓞 E) {u} := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, z, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨o, ho⟩ := hy (Fin.last m)
    have e : proj E m (x + (blk σ c u d).mulVecLin.restrictScalars (𝓞 E) y)
        = (proj E m x + c.mulVec (proj E m y)) + o • u := by
      funext i
      have := blk_mulVec_castSucc σ c u d y i
      simp only [proj_apply, Pi.add_apply, map_add, LinearMap.restrictScalars_apply,
        Matrix.mulVecLin_apply, Pi.smul_apply, Algebra.smul_def, ho]
      rw [this, add_assoc]
      rfl
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
    exact Submodule.add_mem _ (intVec_le_lam c (proj_mem_intVec hx))
      (mulVec_mem_lam c (proj_mem_intVec hy))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [← map_proj_intVec m]
      exact Submodule.map_mono (intVec_le_lam _)
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E 0)),
        mulVec_mem_lam _ (snoc_mem_intVec hy 0), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) 0 (algebraMap (𝓞 E) E 1)),
        mulVec_mem_lam _ (snoc_mem_intVec (Submodule.zero_mem _) 1), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp [show (fun _ : Fin m => (0 : E)) = 0 from rfl]

theorem relIndex_lam_sup {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) :
    (lam c).toAddSubgroup.relIndex (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = Ideal.absNorm (tor c u) := by
  let φ : 𝓞 E →+ (Fin m → E) := (LinearMap.toSpanSingleton (𝓞 E) _ u).toAddMonoidHom
  have hsup : (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = (lam c).toAddSubgroup ⊔ (⊤ : AddSubgroup (𝓞 E)).map φ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
      exact AddSubgroup.add_mem_sup ha ⟨t, trivial, rfl⟩
    · refine sup_le (fun x hx => Submodule.mem_sup_left hx) ?_
      rintro _ ⟨t, -, rfl⟩
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hcomap : (lam c).toAddSubgroup.comap φ = (tor c u).toAddSubgroup := by
    ext t
    change t • u ∈ lam c ↔ t ∈ tor c u
    rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  rw [hsup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.relIndex_comap, hcomap,
    AddSubgroup.relIndex_top_right]
  rfl

def lastInc (E : Type) [Field E] [NumberField E] (m : ℕ) : E →+ (Fin (m + 1) → E) :=
  (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m)).toAddMonoidHom

theorem comap_lastInc_intVec (m : ℕ) :
    (intVec E (m + 1)).toAddSubgroup.comap (lastInc E m)
      = (1 : Submodule (𝓞 E) E).toAddSubgroup := by
  ext x
  change (Pi.single (Fin.last m) x : Fin (m + 1) → E) ∈ intVec E (m + 1) ↔
    x ∈ (1 : Submodule (𝓞 E) E)
  rw [Submodule.mem_one]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h (Fin.last m)
    exact ⟨o, by simpa using ho⟩
  · rintro ⟨o, rfl⟩ i
    by_cases hi : i = Fin.last m
    · subst hi
      exact ⟨o, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hi]⟩

theorem map_lastInc_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).toAddSubgroup.map (lastInc E m)
      = (lam C).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [AddMonoidHom.mem_ker]
    funext i
    simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last]
  · intro hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hv
    rw [AddMonoidHom.mem_ker] at h2
    have hv' : lastInc E m (v (Fin.last m)) = v := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastInc]
      · have := congrFun h2 j
        simp only [LinearMap.toAddMonoidHom_coe, proj_apply, Pi.zero_apply] at this
        simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last, this]
    refine ⟨v (Fin.last m), ?_, hv'⟩
    change lastInc E m (v (Fin.last m)) ∈ lam C
    rw [hv']
    exact h1

theorem delta_blk (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  have hC := (GlobalTheory.T.delta_eq_lattice_index E (m + 1) (blk σ c u d)).2
  have hc := (GlobalTheory.T.delta_eq_lattice_index E m c).2
  have hsplit := relIndex_split (proj E m).toAddMonoidHom (intVec E (m + 1)).toAddSubgroup
    (lam (blk σ c u d)).toAddSubgroup (intVec_le_lam (blk σ c u d))
  have hA : (intVec E (m + 1)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (intVec E m).toAddSubgroup := by
    rw [← map_proj_intVec m]; rfl
  have hB : (lam (blk σ c u d)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup := by
    rw [← map_proj_lam σ c u d]; rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex (intVec E m).toAddSubgroup
    (lam c).toAddSubgroup (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
    (intVec_le_lam c) (fun x hx => Submodule.mem_sup_left hx)
  have hfib : (intVec E (m + 1)).toAddSubgroup.relIndex
      ((lam (blk σ c u d)).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker)
      = idx E (lastFib (blk σ c u d)) := by
    rw [← map_lastInc_lastFib, ← AddSubgroup.relIndex_comap, comap_lastInc_intVec]
    rfl
  rw [hC, hc, hsplit, hA, hB, hfib, ← hmul, relIndex_lam_sup]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp

def IsI {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x

section I

variable {K : Type} [Field K] [NumberField K]

theorem IsI.add {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x + y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o + p, by simp⟩

theorem IsI.neg {x : K} (hx : IsI x) : IsI (-x) := by
  obtain ⟨o, rfl⟩ := hx
  exact ⟨-o, by simp⟩

theorem IsI.sub {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsI.mul {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x * y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o * p, by simp⟩

theorem isI_zero : IsI (0 : K) := ⟨0, by simp⟩

theorem isI_sum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsI (f i)) :
    IsI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isI_zero : IsI (0 : K))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Kc_le_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc c ≤ Kc (c + h) := by
  intro y hy i
  have h1 : IsI ((c *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := hy i
  have h2 : IsI ((h *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := by
    show IsI (∑ j, h i j * algebraMap (𝓞 K) K (y j))
    exact isI_sum (K := K) Finset.univ _ fun j _ => (hh i j).mul ⟨y j, rfl⟩
  have h3 := h1.add h2
  rw [Matrix.add_mulVec]
  exact h3

theorem Kc_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc (c + h) = Kc c := by
  refine le_antisymm ?_ (Kc_le_add c h hh)
  have := Kc_le_add (c + h) (-h) fun a b => by simpa using IsI.neg (hh a b)
  simpa using this

theorem delta_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    delta (c + h) = delta c := by
  unfold delta
  rw [Kc_add c h hh]

theorem vec_out {m : ℕ} (t : Fin m → K) (i : Fin m) :
    IsI ((Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) : Fin m → K) i - t i) := by
  have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m))
      = (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) := Quotient.out_eq _
  have h2 := (Submodule.Quotient.eq _).1 h
  exact h2 i

end I

section H

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField E]

theorem herm_out (σ : E →ₐ[F] E) {n : ℕ} (t : hermE σ n) (a b : Fin n) :
    IsI ((Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) :
      hermE σ n ⧸ hermO σ n) = QuotientAddGroup.mk t := Quotient.out_eq _
  have h2 : IsI ((-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b) :=
    (QuotientAddGroup.eq.1 h) a b
  have h3 := h2.neg
  have e : -(-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b =
      (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b := by
    simp
    ring
  rwa [e] at h3

def topB (σ : E →ₐ[F] E) {m : ℕ} (C : hermE σ (m + 1)) : hermE σ m :=
  ⟨fun a b => C.1 a.castSucc b.castSucc, fun a b => C.2 a.castSucc b.castSucc⟩

def lastCol {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Fin m → E :=
  fun a => C a.castSucc (Fin.last m)

theorem blk_cc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a b : Fin m) : blk σ c u d a.castSucc b.castSucc = c a b := by simp [blk]

theorem blk_cl (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a : Fin m) : blk σ c u d a.castSucc (Fin.last m) = u a := by simp [blk]

theorem blk_lc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (b : Fin m) : blk σ c u d (Fin.last m) b.castSucc = σ (u b) := by simp [blk]

theorem blk_ll (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    blk σ c u d (Fin.last m) (Fin.last m) = d := by simp [blk]

theorem blk_sub_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (C : hermE σ (m + 1)) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (hc : ∀ a b : Fin m, IsI (c a b - C.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (u a - C.1 a.castSucc (Fin.last m)))
    (hd : IsI (d - C.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) :
    IsI (blk σ c u d i j - C.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact hd
    | cast b =>
      rw [blk_lc, ← C.2 (Fin.last m) b.castSucc, ← map_sub]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl]; exact hu a
    | cast b => rw [blk_cc]; exact hc a b

theorem herm_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (D : hermE σ (m + 1))
    (hc : ∀ a b : Fin m, IsI (D.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (D.1 a.castSucc (Fin.last m)))
    (hd : IsI (D.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) : IsI (D.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hd
    | cast b =>
      rw [← D.2 (Fin.last m) b.castSucc]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => exact hu a
    | cast b => exact hc a b

end H

theorem isI_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {y : F} (hy : IsI y) : IsI (algebraMap F E y) := by
  obtain ⟨o, rfl⟩ := hy
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F o)) :=
    (RingOfIntegers.isIntegral_coe o).algebraMap
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ h⟩

theorem hermClass_blocks : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  intro F E _ _ _ _ _ σ hcm m
  obtain ⟨-, hfix, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  have hσ : ∀ x : E, IsI x → IsI (σ x) := by
    rintro x ⟨o, rfl⟩
    exact ⟨sO σ o, hsO o⟩
  have hcorner : ∀ C : hermE σ (m + 1), ∃ y : F,
      algebraMap F E y = C.1 (Fin.last m) (Fin.last m) := fun C => hfix _ (C.2 _ _)
  choose dd hdd using hcorner
  refine ⟨fun x => (QuotientAddGroup.mk (topB σ (Quotient.out x)),
    Submodule.Quotient.mk (lastCol (Quotient.out x).1),
    Submodule.Quotient.mk (fun _ => dd (Quotient.out x))), ?_, ?_⟩
  · intro x x' hxx
    obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := by simpa [Prod.ext_iff] using hxx
    have h1' := QuotientAddGroup.eq.1 h1
    have h2' := (Submodule.Quotient.eq _).1 h2
    have h3' := (Submodule.Quotient.eq _).1 h3
    rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    refine QuotientAddGroup.eq.2 ?_
    refine fun i j => herm_isI σ hσ (-(Quotient.out x) + Quotient.out x') ?_ ?_ ?_ i j
    · intro a b
      exact h1' a b
    · intro a
      have : IsI (lastCol (Quotient.out x).1 a - lastCol (Quotient.out x').1 a) := h2' a
      have e := this.neg
      simpa [lastCol, add_comm, sub_eq_add_neg] using e
    · have : IsI (dd (Quotient.out x) - dd (Quotient.out x')) := h3' 0
      have e := (isI_algebraMap (E := E) this).neg
      simpa [hdd, add_comm, sub_eq_add_neg] using e
  · intro x
    dsimp only
    set C := Quotient.out x with hC
    set M := blk σ (Quotient.out (QuotientAddGroup.mk (topB σ C) : hermE σ m ⧸ hermO σ m)).1
      (Quotient.out (Submodule.Quotient.mk (lastCol C.1) : (Fin m → E) ⧸ intVec E m))
      (algebraMap F E ((Quotient.out (Submodule.Quotient.mk (fun _ => dd C) : FQ F) : Fin 1 → F) 0))
      with hM
    have hI : ∀ i j, IsI ((M - C.1) i j) := by
      intro i j
      refine blk_sub_isI σ hσ C _ _ _ ?_ ?_ ?_ i j
      · intro a b
        exact herm_out σ (topB σ C) a b
      · intro a
        exact vec_out (lastCol C.1) a
      · have h := isI_algebraMap (E := E) (vec_out (fun _ : Fin 1 => dd C) 0)
        rw [map_sub, hdd] at h
        exact h
    have := delta_add C.1 (M - C.1) hI
    rw [add_sub_cancel] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_coset_twisted_conjugacy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.SuppCent.main | exact GlobalTheory.CompanionTheory.SuppCent.main | (intros; apply GlobalTheory.CompanionTheory.SuppCent.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem clsZ_mem_Ff_succ {R : Type} [CommRing R] (K : DCx.{w} R) {n p q : ℕ} (hpq : p + q = n)
    (hS : Subsingleton ((K.col p).H q)) (z : Zf K n p) : clsZ K n p z ∈ Ff K n (p + 1) := by
  have hv : (K.col p).d q (z.1.1.1 p q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) p q z.2
  have h1 : (K.col p).cls (z.1.1.1 p q) hv = 0 := Subsingleton.elim _ _
  rw [(P.cls_surj _ q).2.1] at h1
  obtain ⟨W, hW, hl⟩ := lower_vert K z.1.1.1 z.1.1.2 hpq z.2 0 0 (fun _ _ _ => rfl) (by simp)
    (by simpa using h1)
  exact lower K z W hW hl

theorem Ff_eq_top_of_acyclic {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (h : ∀ p q, a < q → Subsingleton ((K.col p).H q)) : ∀ p, p ≤ j → Ff K (a + j) p = ⊤ := by
  intro p
  induction p with
  | zero =>
    intro _
    refine (Submodule.eq_top_iff').2 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨⟨z, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩, rfl⟩
  | succ p ih =>
    intro hp
    refine (Submodule.eq_top_iff').2 fun x => ?_
    have hx : x ∈ Ff K (a + j) p := by rw [ih (by omega)]; exact Submodule.mem_top
    obtain ⟨z, rfl⟩ := hx
    exact clsZ_mem_Ff_succ K (q := a + j - p) (by omega) (h p _ (by omega)) z

theorem clsZ_surjective_of_acyclic : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  intro R _ K a j h
  exact LinearMap.range_eq_top.1 (Ff_eq_top_of_acyclic K a j h j le_rfl)

end GlobalTheory.CompanionTheory.CechSerre
end

