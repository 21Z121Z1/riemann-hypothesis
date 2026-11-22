import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeLayerCoverBasisModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovLayer

open GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime]

theorem sumZ {Γ V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (v : Γ → V) (F : Γ →₀ ℤ_[l]) : (F.sum fun g c => zOm l c • v g) = Finsupp.linearCombination ℤ_[l] v F := by
  simp only [Finsupp.linearCombination_apply, zOm_smul]

theorem sumZ_fin {ι V : Type} [Fintype ι] [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] (Om l) V] (v : ι → V) (w : ι → ℤ_[l]) : ∑ i, zOm l (w i) • v i = ∑ i, w i • v i := by
  simp only [zOm_smul]

theorem lpow_smul {V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (N : ℕ) (x : V) : (l : Om l) ^ N • x = ((l : ℤ_[l]) ^ N) • x := by
  rw [← zOm_smul]; simp [zOm, map_pow, map_natCast]

theorem coord_unique {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] {b : ι → V} (hb : LinearIndependent ℚ_[l] b) {v w : ι → ℤ_[l]}
    (h : ∑ i, v i • b i = ∑ i, w i • b i) : v = w := by
  have hz : LinearIndependent ℤ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).2 hb
  funext i
  exact Fintype.linearIndependent_iffₛ.1 hz v w h i

theorem lc_translate {Γ A : Type} [Group Γ] [Ring A] [Module ℤ_[l] A] [SMulCommClass ℤ_[l] A A]
    [IsScalarTower ℤ_[l] A A] (v : Γ → A) (hv : ∀ g h, v (g * h) = v g * v h) (g : Γ) (F : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] v (F.mapDomain (g * ·)) = v g * Finsupp.linearCombination ℤ_[l] v F := by
  rw [Finsupp.linearCombination_mapDomain]
  have : (v ∘ (g * ·)) = (LinearMap.mulLeft ℤ_[l] (v g)) ∘ v := by funext h; simp [hv]
  rw [this, ← Finsupp.apply_linearCombination]
  rfl

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    tup ρs (g * h) = tup ρs g * tup ρs h := by
  funext k; simp [tup, map_mul, Units.val_mul]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) : tup ρs 1 = 1 := by
  funext k; simp [tup]

theorem coordsB {Γ : Type} [Group Γ] {a d : ℕ} {ρ : Γ →* GL (Fin d) ℤ_[l]} {r : Γ →* GL (Fin a) (Om l)}
    {b : Fin d → Matrix (Fin a) (Fin a) (Om l)} {e : Fin d → ℤ_[l]} (hR : Reads ρ r b e) (f : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f =
      ∑ i, (f.sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
  have key : ∀ h, ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ∑ i, (∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
    intro h
    have h1 := hR.one
    have h2 := hR.equi h
    simp only [zOm_smul] at h1 h2
    calc ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = (r h).val * ∑ j, e j • b j := by
          rw [h1, Matrix.mul_one]
      _ = ∑ j, e j • ((r h).val * b j) := by rw [Matrix.mul_sum]; simp only [Matrix.mul_smul]
      _ = ∑ j, e j • ∑ i, ((ρ h).val i j) • b i := by simp only [h2]
      _ = _ := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single h c =>
    rw [Finsupp.linearCombination_single, key h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_single_index (by simp), smul_smul]

theorem layer : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → LinearIndependent ℚ_[l] b → (∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ c : ℕ, (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → ∀ (n N : ℕ), n ≤ N → (∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ N • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹) → ∀ (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, Continuous (ρs k)) → (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∀ cs : Fin m → Om l, (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (L k).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb P N ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ _ a r d ρ b e hR hind hspan c hlow n N hnN hN m ρs L t hcont hρL htL hLspan hone hstab cs happ
  obtain ⟨u, hu⟩ := GlobalTheory.T.galoisRepTuple_span_saturation_bound l Γ a m ρs t hone hstab
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.trace_estimate_scaledProductSpanLattice l Γ a r m ρs t c N n cs hnN happ
  refine ⟨max (N + u) M₁, fun M hM => ?_⟩
  have hMu : N + u ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : M₁ ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hstL, hstT⟩ := GlobalTheory.T.scaledProductSpanLattice_stable_galoisRepTuple l Γ a m ρs t M hstab
  obtain ⟨hentT, hspT⟩ := GlobalTheory.T.scaledProductSpanLattice_entries_and_span l Γ a m ρs L t M hρL htL hLspan
  obtain ⟨d', bb, hbbind, hbbmem, hbbco⟩ := GlobalTheory.T.scaledProductSpanLattice_exists_padic_basis l Γ a m ρs t M hone hstab
  obtain ⟨ρ', hρ'c, hact⟩ := GlobalTheory.T.continuous_rep_of_matrixTuple_padic_basis l Γ a m ρs (latT ρs t M) d' bb hcont hbbind hbbmem hbbco hstT
  have hW : ∀ H : Γ →₀ ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) H ∈ latL t M →
      ∃ w : Fin d → ℤ_[l], Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) H = (l : Om l) ^ N • ∑ i, w i • b i := by
    intro H hH
    rw [← sumZ] at hH
    obtain ⟨H', hH'⟩ := hu N M hMu H hH
    rw [sumZ, sumZ, lpow_smul] at hH'
    obtain ⟨f', hf'⟩ := GlobalTheory.T.galoisRepTuple_relation_mem_pow_span l Γ a r m ρs c N cs hlow happ (H - (l : ℤ_[l]) ^ N • H') (by
      rw [sumZ, map_sub, map_smul, hH', sub_self])
    rw [sumZ, sumZ, map_sub, map_smul, lpow_smul] at hf'
    refine ⟨fun i => (f' + H').sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j, ?_⟩
    rw [← coordsB hR (f' + H'), map_add, lpow_smul, smul_add, ← hf', sub_add_cancel]
  have hdec : ∀ s, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M ∧ bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) F + y := by
    intro s
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hbbmem s)
    obtain ⟨F, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨F, y, hy, by rw [← hxy, Finsupp.linearCombination_apply]⟩
  choose F y hy hFy using hdec
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin d) (Fin d') ℤ_[l], ∀ s, ∑ i, P i s • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (F s) :=
    ⟨Matrix.of fun i s => (F s).sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j,
      fun s => (coordsB hR (F s)).symm⟩
  have hPz : ∀ z : Fin d' → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (∑ s, z s • F s) := by
    intro z
    simp only [map_sum, map_smul, ← hP, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hCar : ∀ (z : Fin d' → ℤ_[l]) (G : Γ →₀ ℤ_[l]) (y0 : Fin m → Matrix (Fin a) (Fin a) (Om l)), y0 ∈ latL t M →
      ∑ s, z s • bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) G + y0 →
      ∃ w : Fin d → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) G + (l : Om l) ^ N • ∑ i, w i • b i := by
    intro z G y0 hy0 heq
    obtain ⟨w, hw⟩ := hW (∑ s, z s • F s - G) (by
      have hLF : ∀ s, Finsupp.linearCombination ℤ_[l] (tup ρs) (F s) = bb s - y s := fun s => by rw [hFy s]; abel
      have : Finsupp.linearCombination ℤ_[l] (tup ρs) (∑ s, z s • F s - G) = y0 - ∑ s, z s • y s := by
        rw [map_sub, map_sum]
        simp only [map_smul, hLF, smul_sub, Finset.sum_sub_distrib, heq]
        abel
      rw [this]
      exact Submodule.sub_mem _ hy0 (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hy s)))
    refine ⟨w, ?_⟩
    rw [hPz, ← hw, map_sub]
    abel

  have h1T : (1 : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ latT ρs t M := by rw [← tup_one ρs]; exact tup_mem_latT ρs t M 1
  obtain ⟨e', he'⟩ := hbbco 1 h1T
  have hrb : ∀ g (v : Fin d → ℤ_[l]), ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ∑ s, v s • b s =
      ∑ i, (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ v) i • b i := by
    intro g v
    have h2 := hR.equi g
    simp only [zOm_smul] at h2
    rw [Matrix.mul_sum]
    simp only [Matrix.mul_smul, h2, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hrmul : ∀ g h, ((r (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := fun g h => by simp [map_mul, Units.val_mul]
  refine ⟨d', ρ', bb, e', P, hρ'c, fun s k i j => hentT _ (hbbmem s) k i j, hbbind, ?_, ?_, hbbmem, hbbco, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine Submodule.span_le.2 ?_ (hspT x hx)
    intro v hv
    obtain ⟨z, rfl⟩ := hbbco v hv
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [show zOm l (z s) = algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] (z s)) from rfl, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · intro k
    constructor
    · intro g j
      have := congrFun (hact g j) k
      simpa only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, tup] using this
    · have := congrFun he'.symm k
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.one_apply] using this
  · intro z G y0 hy0 heq
    rw [sumZ_fin, sumZ] at heq
    obtain ⟨w, hw⟩ := hCar z G y0 hy0 heq
    exact ⟨w, by rw [sumZ_fin, sumZ, sumZ_fin]; exact hw⟩
  · constructor
    · intro g i j
      have hz := hact g j
      rw [sumZ_fin] at hz
      obtain ⟨w, hw⟩ := hCar (fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j)
        ((F j).mapDomain (g * ·)) (tup ρs g * y j) (hstL g _ (hy j)) (by
          rw [← hz, lc_translate _ (tup_mul ρs) g, hFy j, mul_add])
      rw [lc_translate _ hrmul g, ← hP j, hrb, lpow_smul, Finset.smul_sum, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) i j =
          (P *ᵥ fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have e2 : (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) * P) i j =
          (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ fun s => P s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, e2, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
    · have hb : ∀ j, ∃ f : Γ →₀ ℤ_[l], b j = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f := fun j => by
        obtain ⟨f, hf⟩ := hspan j
        exact ⟨f, by rw [hf, sumZ]⟩
      choose f hf using hb
      have hz : ∀ j, ∃ z : Fin d' → ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) = ∑ s, z s • bb s := fun j => by
        obtain ⟨z, hz⟩ := hbbco _ (Submodule.mem_sup_left (Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨f j, by rw [Finsupp.linearCombination_apply]⟩) : Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) ∈ latT ρs t M)
        exact ⟨z, by rw [hz, sumZ_fin]⟩
      choose z hz using hz
      refine ⟨Matrix.of fun s j => z j s, fun i j => ?_⟩
      obtain ⟨w, hw⟩ := hCar (z j) (f j) 0 (Submodule.zero_mem _) (by rw [add_zero, hz j])
      rw [← hf j, lpow_smul, Finset.smul_sum] at hw
      have hbj : b j = ∑ i, (1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j • b i := by
        simp [Matrix.one_apply, ite_smul]
      rw [hbj, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * Matrix.of fun s j => z j s) i j = (P *ᵥ z j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro i
    obtain ⟨w, hw⟩ := hCar e' (Finsupp.single 1 1) 0 (Submodule.zero_mem _) (by
      rw [add_zero, Finsupp.linearCombination_single, one_smul, tup_one, he', sumZ_fin])
    rw [Finsupp.linearCombination_single, one_smul, map_one, Units.val_one, ← hR.one, sumZ_fin, lpow_smul,
      Finset.smul_sum, ← Finset.sum_add_distrib] at hw
    simp only [smul_smul, ← add_smul] at hw
    have := congrFun (coord_unique hind hw) i
    rw [Pi.sub_apply, this, add_sub_cancel_left]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro s
    have := hM₁ M hM1 (F s) (y s) (hy s)
    rw [sumZ_fin, hP s, hFy s, ← sumZ, ← sumZ]
    exact this

end GlobalTheory.CovLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem sigA_coeff_pt (g : GQ l) (w : Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) :=
  IsFractionRing.injective (OCb l) (Cb l)
    ((congrArg (WittVector.coeff · n) (galW_inclW g w)).symm.trans (autCb_alg l (galTilt l g) (w.coeff n)))

theorem exists_sigma_pow (g : GQ l) :
    ∃ m : ℕ, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w) := by
  let ρ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)
  have hρ : ∀ x, Fq.val l a (ρ x) = Per.σF g (Fq.val l a x) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ l
  have := Fintype.ofFinite (Fq l a)
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { ρ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod l) (Fq l a))) (algebraMap (ZMod l) _)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) (Fq l a)).2 ψ
  have hpow : ∀ x, ρ x = x ^ l ^ (j : ℕ) := fun x => by
    have h1 : ψ x = x ^ l ^ (j : ℕ) := by
      rw [← hj]
      simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact h1
  refine ⟨j, fun w => WittVector.ext fun n => ?_⟩
  refine (sigA_coeff_pt g (wA l a w) n).trans ?_
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ (j : ℕ)) w).coeff n)
  rw [coeff_sigma_pow, ← hpow, hρ]

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

theorem emb_sigma_pow (m : ℕ) (τ : ZMod a) (w : Wq l a) :
    emb t τ ((sigma l a ^ m) w) = emb t (τ - m) w := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, emb_sigma, ih,
      show τ - 1 - (m : ZMod a) = τ - ((m + 1 : ℕ) : ZMod a) by push_cast; ring]

theorem galOA_constA_shift {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (x : ZMod a → O) :
    galOA O g (constA t x) = constA t fun τ => x (τ - m) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero (constA t)).symm
  | tmul o w =>
    have : (fun τ => splitHom t (o ⊗ₜ w) (τ - m)) = splitHom t (o ⊗ₜ (sigma l a ^ m) w) :=
      funext fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma_pow]
    rw [this, constA_splitHom, constA_splitHom]
    exact (galOA_tmul g o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (hm w))
  | add y y' h h' =>
    rw [map_add, map_add, map_add, h, h', ← map_add]
    rfl

theorem galOA_idem {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (τ : ZMod a) :
    galOA O g (idem (constA t) τ) = idem (constA t) (τ + m) := by
  rw [idem, galOA_constA_shift t hm, idem]
  congr 1
  ext1 σ
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

variable {e : ℕ} [NeZero e] (ϖ : PiSys l e)

theorem kummer_pow {k : GQ l} (hk : k ∈ ϖ.GKinf) : ϖ.kummer k ^ e = 1 := by
  have hfix : ∀ n, k (ϖ.seq n ^ e) = ϖ.seq n ^ e := fun n =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)
  refine Perfection.ext fun n => ?_
  have key : ∀ x : Perfection (ModP (OC l) l) l,
      Perfection.coeff (ModP (OC l) l) l n (x ^ e) = Perfection.coeff (ModP (OC l) l) l n x ^ e :=
    fun x => map_pow _ _ _
  refine (key (ϖ.kummer k)).trans (Eq.trans ?_ (map_one (Perfection.coeff (ModP (OC l) l) l n)).symm)
  change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
  rw [← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))]
  congr 1
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix,
    div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
  rfl

theorem exists_kummer_eq (hsucc : e + 1 = l ^ a) {k : GQ l} (hk : k ∈ ϖ.GKinf) :
    ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k ∧ z ^ e = 1 := by
  have h1 := kummer_pow ϖ hk
  have h2 : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← hsucc, pow_succ, h1, one_mul]
  exact ⟨(⟨_, h2⟩ : Fq l a), rfl, Fq.val_injective l a (((map_pow (Fq.val l a) _ e).trans h1).trans (map_one _).symm)⟩

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

omit [Fact l.Prime] in
theorem rescale_C_eq {R : Type} [CommRing R] (b r : R) : rescale b (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem galOA_evO {k : GQ l} (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (h : O⟦X⟧) :
    galOA O k (ϖ.evO O h) =
      glue (constA t) (ϖ.evO O) fun τ => rescale (emb t τ (WittVector.teichmuller l z)) h := by
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hu : constA t c = 1 ⊗ₜ wA l a (WittVector.teichmuller l z) := constA_emb t _
  have hk : galOA O k (ϖ.teichR O) = constA t c * ϖ.teichR O := by
    rw [ϖ.galOA_teichR O k, hu, PiSys.mu, tmul_sub, ← Algebra.TensorProduct.one_def, add_sub_cancel,
      wA_teich, hz]
  have hX' : ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) X = constA t c * ϖ.teichR O := by
    change galOA O k (ϖ.evO O X) = _
    rw [PiSys.evO_X, hk]
  refine RingHom.congr_fun (ringHom_ext_of_sep ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom)
    ((glue (constA t) (ϖ.evO O)).toRingHom.comp (Pi.ringHom fun τ => rescale (c τ))) (fun r => ?_) ?_ ?_) h
  · change galOA O k (ϖ.evO O (C r)) = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) (C r))
    simp only [rescale_C_eq]
    rw [glue_const]
    have h2 : ϖ.evO O (C r) = algebraMap O _ r := (ϖ.evO O).commutes r
    rw [h2, AlgHom.commutes]
  · rw [hX']
    change _ = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) X)
    simp only [rescale_X]
    rw [glue_apply, eq_sum_idem (constA t) c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, PiSys.evO_X, show ϖ.evO O (C (c τ)) = algebraMap O _ (c τ) from (ϖ.evO O).commutes _,
      mul_assoc]
  · intro x hx
    refine ϖ.sep_teichR O x fun n => ?_
    obtain ⟨y, hy⟩ := hx n
    exact ⟨constA t c ^ n * y, by rw [hy, hX', mul_pow]; ring⟩

variable (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem exists_covers {k : GQ l} (hk : k ∈ ϖ.GKinf) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  obtain ⟨m, hm⟩ := exists_sigma_pow (a := a) k
  obtain ⟨z, hz, hze⟩ := exists_kummer_eq (a := a) ϖ (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)) hk
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩, fun f f' hf' => ?_⟩
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hm, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz, idem_mul_glue]

end GlobalTheory.KinfCover

open GlobalTheory.KinfCover in

theorem GlobalTheory.KinfCover.exists_covers_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ hk => exists_covers t ϖ K hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPeriodMatrixOfFinrank
section
open TensorProduct Module

noncomputable section

namespace GlobalTheory.RegularRing

theorem exists_periodMatrix_of_finrank (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B]
    (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F)
    (hA : ∀ g, (A g).det ≠ 0) (hE : ∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b)
    (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b)
    (W : Submodule F (n → B))
    (hW : ∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x)
    (hdim : finrank F ↥W = finrank F E * Fintype.card n) :
    ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  classical
  by_cases hn : IsEmpty n
  · refine ⟨1, fun g => ?_⟩
    ext i
    exact isEmptyElim i
  rw [not_isEmpty_iff] at hn
  let WE : Submodule E (n → B) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        intro c x hx
        rw [SetLike.mem_coe, hW] at hx ⊢
        intro g
        have h1 : (fun i => act g ((c • x) i)) = algebraMap E B c • fun i => act g (x i) := by
          funext i
          simp [Algebra.smul_def, hE]
        rw [h1, Matrix.mulVec_smul, hx g]
        funext i
        simp [Algebra.smul_def] }
  have hWE : ∀ x, x ∈ WE ↔ x ∈ W := fun x => Iff.rfl
  have hfr : finrank E ↥WE = Fintype.card n := by
    have h1 := Module.finrank_mul_finrank F E ↥WE
    have h2 : finrank F ↥WE = finrank F ↥W :=
      ((Submodule.restrictScalarsEquiv F E (n → B) WE).restrictScalars F).finrank_eq.symm.trans
        (by congr 1)
    rw [h2, hdim] at h1
    exact Nat.eq_of_mul_eq_mul_left finrank_pos h1
  haveI : Module.Finite E ↥WE := Module.finite_of_finrank_pos (by rw [hfr]; exact Fintype.card_pos)
  let b : Basis n E ↥WE := (Module.finBasisOfFinrankEq E ↥WE hfr).reindex (Fintype.equivFin n).symm
  let v : n → (n → B) := fun j => (b j : n → B)
  have hv : ∀ g j, ((A g).map (algebraMap F B)).mulVec (fun i => act g (v j i)) = v j :=
    fun g j => (hW _).1 ((hWE _).1 (b j).2) g
  let σ : G → (n → B) →+ (n → B) := fun g =>
    { toFun := fun x => ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i))
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add]
        exact Matrix.mulVec_add _ _ _ }
  have hσ : ∀ g (c : B) (w : n → B), σ g (c • w) = act g c • σ g w := by
    intro g c w
    change ((A g).map (algebraMap F B)).mulVec (fun i => act g ((c • w) i)) =
      act g c • ((A g).map (algebraMap F B)).mulVec (fun i => act g (w i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hvE : LinearIndependent E v :=
    b.linearIndependent.map' WE.subtype WE.ker_subtype
  have hvB : LinearIndependent B v := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    exact linearIndepOn_of_invariant (fun g c => act g c) σ hσ hreg v hv s (hvE.linearIndepOn _)
  let Q : Matrix n n B := Matrix.of fun i j => v j i
  have hQ : ∀ g, (A g).map (algebraMap F B) * Q.map (act g) = Q := by
    intro g
    ext i j
    have := congrFun (hv g j) i
    rw [Matrix.mul_apply]
    simpa [Q, Matrix.mulVec, dotProduct] using this
  have hdet0 : Q.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext j
    refine Fintype.linearIndependent_iff.1 hvB c ?_ j
    funext i
    have := congrFun hc0 i
    simpa [Q, Matrix.mulVec, dotProduct, mul_comm] using this
  have hdetU : IsUnit Q.det := by
    refine hu _ hdet0 fun g => ?_
    have h2 := congrArg Matrix.det (hQ g)
    rw [Matrix.det_mul] at h2
    have h3 : ((A g).map (algebraMap F B)).det = algebraMap F B (A g).det := (RingHom.map_det _ _).symm
    have h4 : (Q.map (act g)).det = act g Q.det := (RingHom.map_det _ _).symm
    rw [h3, h4] at h2
    refine ⟨(A g).det⁻¹, ?_⟩
    conv_rhs => rw [← h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hA g), map_one, one_mul]
  exact ⟨Matrix.GeneralLinearGroup.mk'' Q hdetU, hQ⟩

end GlobalTheory.RegularRing
end
end

