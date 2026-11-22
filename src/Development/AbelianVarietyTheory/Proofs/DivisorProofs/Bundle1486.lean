import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

theorem natCast_mul_apply (m : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((m : FiniteAdeleRing (𝓞 F) F) * a) v = (m : v.adicCompletion F) * a v := by
  have hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F) := by
    induction m with
    | zero => simp
    | succ n ih => simp [Nat.cast_succ, ih]
  simp [hm]

theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz

theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform.RealSchwartz

private theorem norm_add_smul_single_sub_le_of_hasDerivAt_bound {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) (i : Fin k) (t : Fin k → ℝ) (a : ℝ) :
    ‖φ (t + a • (Pi.single i (1 : ℝ) : Fin k → ℝ)) - φ t‖ ≤ B i * |a| := by
  set e : Fin k → ℝ := Pi.single i (1 : ℝ) with he
  have hder : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ (t + u • e)) (φ' i (t + s • e)) s := by
    intro s
    have h0 : HasDerivAt (fun u : ℝ => φ (t + s • e + u • e)) (φ' i (t + s • e)) (s - s) := by
      rw [sub_self]; exact hd i (t + s • e)
    have h1 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h0 ((hasDerivAt_id' s).sub_const s)
    rw [one_smul] at h1
    have hf : (fun u : ℝ => φ (t + u • e)) = ((fun u : ℝ => φ (t + s • e + u • e)) ∘ fun u : ℝ => u - s) := by
      funext u
      simp only [Function.comp_apply]
      congr 1
      rw [sub_smul]; abel
    rw [hf]
    exact h1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun u : ℝ => φ (t + u • e)) (f' := fun s => φ' i (t + s • e))
    (fun s _ => (hder s).hasDerivWithinAt) (fun s _ => hB i _) convex_univ (Set.mem_univ 0) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem continuous_of_bdd_partials {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) : Continuous φ := by

  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set M : ℝ := ∑ i, B i with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hB0 i
  have hBM : ∀ i, B i ≤ M := fun i => Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)

  have key : ∀ x y : Fin k → ℝ, ‖φ y - φ x‖ ≤ (k * M) * ‖y - x‖ := by
    intro x y
    let p : ℕ → Fin k → ℝ := fun j l => if (l : ℕ) < j then y l else x l
    have hp0 : p 0 = x := by funext l; simp [p]
    have hpk : p k = y := by funext l; simp [p, l.isLt]
    have hstep : ∀ j (hj : j < k), p (j + 1) =
        p j + (y ⟨j, hj⟩ - x ⟨j, hj⟩) • (Pi.single (⟨j, hj⟩ : Fin k) (1 : ℝ) : Fin k → ℝ) := by
      intro j hj
      funext l
      simp only [p, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases h : l = ⟨j, hj⟩
      · subst h; simp
      · have hne : (l : ℕ) ≠ j := fun h' => h (Fin.ext h')
        simp only [h, ↓reduceIte, mul_zero, add_zero]
        by_cases hl : (l : ℕ) < j
        · simp [hl, show (l : ℕ) < j + 1 by omega]
        · simp [hl, show ¬ (l : ℕ) < j + 1 by omega]
    have hind : ∀ j, j ≤ k → ‖φ (p j) - φ x‖ ≤ j * (M * ‖y - x‖) := by
      intro j
      induction j with
      | zero => intro _; simp [hp0]
      | succ j ih =>
        intro hj
        have hjk : j < k := hj
        have h1 := norm_add_smul_single_sub_le_of_hasDerivAt_bound φ φ' hd B hB ⟨j, hjk⟩ (p j) (y ⟨j, hjk⟩ - x ⟨j, hjk⟩)
        rw [← hstep j hjk] at h1
        have hc : |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ ‖y - x‖ := by
          have := norm_le_pi_norm (y - x) ⟨j, hjk⟩
          simpa [Real.norm_eq_abs] using this
        have h2 : B ⟨j, hjk⟩ * |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ M * ‖y - x‖ :=
          mul_le_mul (hBM _) hc (abs_nonneg _) hM0
        calc ‖φ (p (j + 1)) - φ x‖ ≤ ‖φ (p (j + 1)) - φ (p j)‖ + ‖φ (p j) - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ M * ‖y - x‖ + j * (M * ‖y - x‖) := add_le_add (h1.trans h2) (ih (by omega))
          _ = ((j + 1 : ℕ) : ℝ) * (M * ‖y - x‖) := by push_cast; ring
    have := hind k le_rfl
    rw [hpk] at this
    calc ‖φ y - φ x‖ ≤ k * (M * ‖y - x‖) := this
      _ = (k * M) * ‖y - x‖ := by ring
  refine (LipschitzWith.of_dist_le' (K := (k : ℝ) * M) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact key y x

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform.RealSchwartz

variable {F : Type} [Field F] [NumberField F]

theorem continuous_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : v.IsReal
  · have hE := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.1 ⟨v, hv⟩ := by
      funext y
      have h0 := congrArg (fun z => z.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_fst
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have hE := (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbedding v ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.2 ⟨v, hc⟩ := by
      funext y
      have h0 := congrArg (fun z => z.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_snd

theorem embR_add {N : ℕ} (a b : Fin N → mixedEmbedding.mixedSpace F) :
    (embR (a + b) : Fin N → AF F) = embR a + embR b := by
  funext i
  simp only [embR, Pi.add_apply, map_add]
  exact (congrArg (pairA F _) (add_zero (0 : Af F))).symm.trans rfl

theorem embR_zero {N : ℕ} : (embR (0 : Fin N → mixedEmbedding.mixedSpace F) : Fin N → AF F) = 0 := by
  funext i
  simp only [embR, pairA, Pi.zero_apply, map_zero]
  rfl

theorem continuous_embR {N : ℕ} : Continuous (embR : (Fin N → mixedEmbedding.mixedSpace F) → Fin N → AF F) := by
  apply continuous_pi
  intro i
  show Continuous fun t : Fin N → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  exact (continuous_mixedSpace_symm.comp (continuous_apply i)).prodMk continuous_const

theorem fin_embR {N : ℕ} (t : Fin N → mixedEmbedding.mixedSpace F) : fin (embR t : Fin N → AF F) = 0 := by
  funext l
  first
  | rfl
  | simp [fin, embR, pairA, sndA]

def lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : ℝ →+ VA F N where
  toFun s := (embR (s • v), 0)
  map_zero' := by rw [zero_smul, embR_zero]; rfl
  map_add' a b := by rw [add_smul, embR_add, Prod.mk_add_mk, add_zero]

theorem isRealLine_lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : IsRealLine (lineR v) := by
  refine ⟨?_, fun t => ⟨fin_embR (t • v), ?_⟩⟩
  · show Continuous fun s : ℝ => ((embR (s • v), 0) : VA F N)
    exact (continuous_embR.comp (continuous_id.smul continuous_const)).prodMk continuous_const
  · funext l
    first
    | rfl
    | simp [fin, sndA]

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform

open RealSchwartz in

theorem schwartz_invV_realTranslate : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  intro F _ _ N _ ψ lam ν _ 𝓓 _ _ 𝒱 _ hder hdec f hf x

  let E := Fin N → mixedEmbedding.mixedSpace F
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv

  let V : Set ((Fin (Module.finrank ℝ E) → ℝ) → ℂ) :=
    {φ | ∃ g ∈ 𝒱, φ = fun s => invV ψ ν 𝓓 g (x + embR (L s))}

  have hpart : ∀ g ∈ 𝒱, ∀ i : Fin (Module.finrank ℝ E), ∃ g' ∈ 𝒱, ∀ s,
      HasDerivAt (fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))))
        (invV ψ ν 𝓓 g' (x + embR (L s))) 0 := by
    intro g hg i
    obtain ⟨g', hg', hd⟩ := hder g hg (lineR (L (Pi.single i (1 : ℝ)))) (isRealLine_lineR _)
    refine ⟨g', hg', fun s => ?_⟩
    have h := hd (x + embR (L s))
    have heq : (fun u : ℝ => invV ψ ν 𝓓 (heisV ψ (lineR (L (Pi.single i (1 : ℝ))) u) g) (x + embR (L s))) =
        fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))) := by
      funext u
      rw [show lineR (L (Pi.single i (1 : ℝ))) u = (embR (u • L (Pi.single i (1 : ℝ))), 0) from rfl,
        invV_heisV_fst, map_add, map_smul, embR_add, add_assoc]
    rwa [heq] at h

  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨g, hg, rfl⟩
    choose g' hg' hd' using hpart g hg
    have hb : ∀ i, ∃ C : ℝ, ∀ s, ‖invV ψ ν 𝓓 (g' i) (x + embR (L s))‖ ≤ C := by
      intro i
      obtain ⟨C, hC⟩ := hdec (g' i) (hg' i) x 0
      exact ⟨C, fun s => by simpa using hC (L s)⟩
    choose B hB using hb
    exact continuous_of_bdd_partials _ (fun i s => invV ψ ν 𝓓 (g' i) (x + embR (L s)))
      (fun i t => hd' i t) B hB
  have hclosed : ∀ φ ∈ V, ∀ i : Fin (Module.finrank ℝ E), ∃ φ' ∈ V, ∀ s : Fin (Module.finrank ℝ E) → ℝ,
      HasDerivAt (fun u : ℝ => φ (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ))) (φ' s) 0 := by
    rintro φ ⟨g, hg, rfl⟩ i
    obtain ⟨g', hg', hd'⟩ := hpart g hg i
    exact ⟨_, ⟨g', hg', rfl⟩, hd'⟩

  have hdecV : ∀ φ ∈ V, ∀ n : ℕ, ∃ C : ℝ, ∀ s, ‖s‖ ^ n * ‖φ s‖ ≤ C := by
    rintro φ ⟨g, hg, rfl⟩ n
    obtain ⟨C, hC⟩ := hdec g hg x n
    refine ⟨‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C, fun s => ?_⟩
    have hs : ‖s‖ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖ := by
      have h := (L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).le_opNorm (L s)
      simpa using h
    calc ‖s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖
        ≤ (‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖) ^ n *
            ‖invV ψ ν 𝓓 g (x + embR (L s))‖ := by gcongr
      _ = ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n *
            (‖L s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖) := by ring
      _ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C := by
            gcongr
            exact hC (L s)
  obtain ⟨_, hS⟩ := GlobalTheory.Unf.PartialClass.smooth_schwartz _ V hcont hclosed
  obtain ⟨g0, hg0⟩ := hS hdecV _ ⟨f, hf, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g0, fun t => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  show invV ψ ν 𝓓 f (x + embR (L (L.symm t))) = _
  rw [L.apply_symm_apply]

end GlobalTheory.ThetaTransform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

namespace GlobalTheory.TorusHeight

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_shape {n q : ℕ} (X Y' : Matrix (Fin n) (Fin q) ℂ) (Y X' : Matrix (Fin q) (Fin n) ℂ)
    (d d' : Fin q → ℂ) {s : ℝ} (hs : 0 ≤ s) (hd : ∀ i, ‖d i‖ ≤ s) (hd' : ∀ i, ‖d' i‖ ≤ s) :
    (opNorm (1 + X * Matrix.diagonal d * Y + Y' * Matrix.diagonal d' * X') : ℝ) ≤
      1 + (‖X‖ * ‖Y‖ + ‖Y'‖ * ‖X'‖) * s := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, (opNorm M : ℝ) = ‖M‖ := fun M => by
    rw [opNorm, coe_nnnorm]; exact (Matrix.l2_opNorm_def M).symm
  rw [e]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hD : ‖Matrix.diagonal d‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd
  have hD' : ‖Matrix.diagonal d'‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd'
  have h2 : ‖X * Matrix.diagonal d * Y‖ ≤ ‖X‖ * s * ‖Y‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))) (norm_nonneg _))
  have h3 : ‖Y' * Matrix.diagonal d' * X'‖ ≤ ‖Y'‖ * s * ‖X'‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD' (norm_nonneg _))) (norm_nonneg _))
  calc _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X * Matrix.diagonal d * Y‖ + ‖Y' * Matrix.diagonal d' * X'‖ :=
        norm_add₃_le
    _ ≤ 1 + ‖X‖ * s * ‖Y‖ + ‖Y'‖ * s * ‖X'‖ := by linarith
    _ = _ := by ring

theorem le_prod_of_forall_le {q : ℕ} {c : ℝ} (hc : 0 < c) (t : Fin q → ℝ) (ht : ∀ i, c ≤ t i) (k : Fin q) :
    t k * (min 1 c) ^ (q - 1) ≤ ∏ i, t i := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k)]
  have hk : 0 ≤ t k := hc.le.trans (ht k)
  refine mul_le_mul_of_nonneg_left ?_ hk
  have := Finset.prod_le_prod (s := Finset.univ.erase k) (f := fun _ => min 1 c) (g := t) (fun _ _ => hm.le)
    (fun i _ => (min_le_right _ _).trans (ht i))
  simpa [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin] using this

theorem norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_ofReal_inv_sub_one (x : ℝ) : ‖(x : ℂ)⁻¹ - 1‖ = |x⁻¹ - 1| := by
  rw [← Complex.ofReal_inv, norm_ofReal_sub_one]

theorem height_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro F E _ _ _ _ _ σ hcm n J q Xf Yf c hc
  classical
  have hm : 0 < min 1 c := lt_min one_pos hc
  set c0 : ℝ := ((min 1 c) ^ (q - 1))⁻¹ + c⁻¹ + 1 with hc0
  have hc0' : 1 ≤ c0 := by
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    linarith
  let τ0 : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  let K : InfinitePlace F → ℝ := fun w =>
    ‖(Xf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Yf * J).map (τ0 w).1‖ +
      ‖(Yf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Xf * J).map (τ0 w).1‖
  have hK : ∀ w, 0 ≤ K w := fun w => by positivity
  refine ⟨∏ w, (1 + K w * c0), Fintype.card (InfinitePlace F), fun t ht a ha hA => ?_⟩
  set P := ∏ i, t i with hP'
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hc.le.trans (ht i)
  have hs : 0 ≤ c0 * (1 + P) := by positivity
  have hs1 : ∀ k, |t k - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 ≤ t k := hc.le.trans (ht k)
    have h1 := le_prod_of_forall_le hc t ht k
    have hpow : 0 < (min 1 c) ^ (q - 1) := pow_pos hm _
    have h2 : t k ≤ ((min 1 c) ^ (q - 1))⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpow]; exact h1
    have h3 : |t k - 1| ≤ t k + 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : ((min 1 c) ^ (q - 1))⁻¹ * P ≤ c0 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      linarith
    nlinarith
  have hs2 : ∀ k, |(t k)⁻¹ - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 < t k := hc.trans_le (ht k)
    have h1 : (t k)⁻¹ ≤ c⁻¹ := inv_anti₀ hc (ht k)
    have h0 : 0 ≤ (t k)⁻¹ := inv_nonneg.2 htk.le
    have h3 : |(t k)⁻¹ - 1| ≤ (t k)⁻¹ + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    nlinarith

  have hfin : ∀ v, htFin F v (matHom _ σ J (proj σ J v a)) = 1 := fun v => by
    rw [mem_infPts_iff_forall.1 ha v, map_one]
    exact htOf_eq_one.2 ⟨by simpa using normFin_one_le (E := E) F v, by simpa using normFin_one_le (E := E) F v⟩

  have hinf : ∀ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
    intro w
    obtain ⟨h1, h2⟩ := hA w (τ0 w)
    have e1 : normInf F w ((matHom _ σ J (projArch σ J w a) : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) = opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) :=
      normInf_eq_opNorm hcm (τ0 w) _
    have e2 : normInf F w (((matHom _ σ J (projArch σ J w a))⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) =
        opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) := by
      rw [← map_inv, ← map_inv]; exact normInf_eq_opNorm hcm (τ0 w) _
    have B1 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h1]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs1 i
      · rw [norm_ofReal_inv_sub_one]; exact hs2 i
    have B2 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h2]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs2 i
      · rw [norm_ofReal_inv_sub_one, inv_inv]; exact hs1 i
    have hfin' : (1 + K w * (c0 * (1 + P))) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    have hone : (1 : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    simp only [htInf, htOf, NNReal.coe_max, NNReal.coe_one]
    rw [e1, e2]
    exact max_le hone (max_le (B1.trans hfin') (B2.trans hfin'))
  have hh : (height σ J a : ℝ) = ∏ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) := by
    rw [height_eq]
    simp only [hfin, finprod_one, mul_one, NNReal.coe_prod]
  rw [hh]
  calc _ ≤ ∏ w, ((1 + K w * c0) * (1 + P)) :=
        Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) (fun w _ => hinf w)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end GlobalTheory.TorusHeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigenStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorusElement_inv_finitePart_one_dualFrame_eigen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  first | exact @GlobalTheory.TorusInv.torus_inv | exact GlobalTheory.TorusInv.torus_inv | (intros; apply GlobalTheory.TorusInv.torus_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArcStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  first | exact @GlobalTheory.CartanConjSkew.conj_skew | exact GlobalTheory.CartanConjSkew.conj_skew | (intros; apply GlobalTheory.CartanConjSkew.conj_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponentStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothing_norm_le_height_pow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) → ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.smoothing_growth_exponent | exact GlobalTheory.AutGrowth.smoothing_growth_exponent | (intros; apply GlobalTheory.AutGrowth.smoothing_growth_exponent <;> assumption)
end

