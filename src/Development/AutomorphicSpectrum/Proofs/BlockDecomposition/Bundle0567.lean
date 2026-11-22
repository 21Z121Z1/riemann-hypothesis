import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMulSupportBnd
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GaugeSpan

open Ad3 Ad3.GP

def bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : ℝ := ∏ᶠ v : Pl, max ‖y v‖ 1

theorem norm_le_one_of_mem {v : Pl} {x : Qv v} (h : x ∈ v.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v).1 h)

theorem finite_mulSupport_bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    (Function.mulSupport fun v : Pl => max ‖y v‖ 1).Finite := by
  have h : ∀ᶠ v : Pl in cofinite, max ‖y v‖ 1 = 1 := by
    filter_upwards [y.2] with v hv
    exact max_eq_right (norm_le_one_of_mem hv)
  exact Filter.eventually_cofinite.1 h

theorem one_le_bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : 1 ≤ bnd y := by
  rw [bnd, finprod_eq_prod _ (finite_mulSupport_bnd y)]
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun v _ => le_max_right _ _

theorem local_le {v : Pl} (x y : Qv v) (h : y - x ∈ v.adicCompletionIntegers ℚ) :
    max ‖y‖ 1 ≤ max ‖x‖ 1 := by
  have h1 : ‖y - x‖ ≤ 1 := norm_le_one_of_mem h
  have h2 : ‖y‖ ≤ max ‖x‖ ‖y - x‖ := by
    have := IsUltrametricDist.norm_add_le_max x (y - x)
    simpa using this
  refine max_le (h2.trans (max_le (le_max_left _ _) (h1.trans (le_max_right _ _)))) (le_max_right _ _)

theorem bnd_le (x y : FiniteAdeleRing (𝓞 ℚ) ℚ) (h : ∀ v : Pl, y v - x v ∈ v.adicCompletionIntegers ℚ) :
    bnd y ≤ bnd x := by
  classical
  set S := (finite_mulSupport_bnd x).toFinset ∪ (finite_mulSupport_bnd y).toFinset with hS
  rw [bnd, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => by positivity) fun v _ => local_le _ _ (h v)

theorem finiteModule_le_bnd (a : IdeleGroup ℚ) : IdeleGroup.finiteModule a ≤ bnd (a : 𝔸[ℚ]).2 := by
  classical
  set S := (IdeleGroup.finite_mulSupport_norm a).toFinset ∪
    (finite_mulSupport_bnd (a : 𝔸[ℚ]).2).toFinset with hS
  rw [IdeleGroup.finiteModule, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => le_max_left _ _

theorem nhds_mem (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    {y : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, y v - x v ∈ v.adicCompletionIntegers ℚ} ∈ 𝓝 x := by
  have ho : IsOpen {z : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, z v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y - x := continuous_id.sub continuous_const
  refine (ho.preimage hc).mem_nhds ?_
  intro v
  simp only [sub_self]
  exact zero_mem (v.adicCompletionIntegers ℚ)

theorem bnd_bdd (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ Ω, bnd y ≤ B := by
  refine hΩ.induction_on (p := fun S => ∃ B : ℝ, 0 < B ∧ ∀ y ∈ S, bnd y ≤ B)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨B, hB, h⟩
    exact ⟨B, hB, fun y hy => h y (hst hy)⟩
  · rintro s t ⟨B, hB, h⟩ ⟨B', _, h'⟩
    refine ⟨max B B', lt_max_of_lt_left hB, ?_⟩
    rintro y (hy | hy)
    · exact (h y hy).trans (le_max_left _ _)
    · exact (h' y hy).trans (le_max_right _ _)
  · intro x _
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (nhds_mem x), bnd x, lt_of_lt_of_le one_pos (one_le_bnd x), ?_⟩
    intro y hy
    exact bnd_le x y hy

theorem module_le (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : IdeleGroup ℚ, (a : 𝔸[ℚ]).2 ∈ Ω → ∀ w : InfinitePlace ℚ,
      (IdeleGroup.ideleModule ℚ a : ℝ) ≤ B * (1 + ‖(a : 𝔸[ℚ]).1 w‖) := by
  obtain ⟨B, hB, h⟩ := bnd_bdd Ω hΩ
  refine ⟨B, hB, fun a ha w => ?_⟩
  have hw : w.IsReal := by
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  have hinf : IdeleGroup.infiniteModule a = ‖(a : 𝔸[ℚ]).1 w‖ := by
    rw [IdeleGroup.infiniteModule, Fintype.prod_subsingleton _ w, InfinitePlace.mult, if_pos hw, pow_one]
  rw [IdeleGroup.ideleModule_apply, hinf, mul_comm]
  have h1 := (finiteModule_le_bnd a).trans (h _ ha)
  have h2 : 0 ≤ ‖(a : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  nlinarith [IdeleGroup.finiteModule_pos a]

def GaugeAt (W : G3 → ℂ) (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (T : ℕ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)

theorem real_step (C A P Q : ℝ) (T d N : ℕ) (hA : 0 < A) (hP : 0 < P) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (h : A ≤ Q * P) : C / A ^ T / P ^ (N + d) ≤ C * Q ^ d / A ^ (T + d) / P ^ N := by
  have h1 : A ^ d ≤ Q ^ d * P ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hA.le h d
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 ≤ C * (A ^ T * P ^ N) := by positivity
  calc C * (A ^ (T + d) * P ^ N) = C * (A ^ T * P ^ N) * A ^ d := by ring
    _ ≤ C * (A ^ T * P ^ N) * (Q ^ d * P ^ d) := mul_le_mul_of_nonneg_left h1 h2
    _ = C * Q ^ d * (A ^ T * P ^ (N + d)) := by ring

theorem GaugeAt.mono {W : G3 → ℂ} {Ω Ω' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} {T T' : ℕ}
    (h : GaugeAt W Ω T) (hΩ : IsCompact Ω) (hs : Ω ⊆ Ω') (hT : T ≤ T') : GaugeAt W Ω' T' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
  obtain ⟨B, hB, hmod⟩ := module_le Ω hΩ
  intro N
  obtain ⟨C, hC⟩ := h (N + d)
  refine ⟨max C 0 * (B * B) ^ d, fun a b k hk w => ?_⟩
  obtain ⟨h1, h2⟩ := hC a b k hk w
  have hA : 0 < (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b :=
    mul_pos (IdeleGroup.ideleModule ℚ a).2 (IdeleGroup.ideleModule ℚ b).2
  have ha0 : 0 ≤ ‖(a : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖(b : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  have hP : 0 < (1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖) := by positivity
  refine ⟨?_, fun hne => ⟨hs (h2 hne).1, hs (h2 hne).2⟩⟩
  by_cases h0 : W (dg (a * b) b 1 * k) = 0
  · rw [h0, norm_zero]
    have : 0 ≤ max C 0 := le_max_right _ _
    positivity
  · obtain ⟨ha, hb⟩ := h2 h0
    have hma := hmod a ha w
    have hmb := hmod b hb w
    have hle : (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b ≤
        B * B * ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) := by
      calc (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b
          ≤ (B * (1 + ‖(a : 𝔸[ℚ]).1 w‖)) * (B * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) :=
            mul_le_mul hma hmb (IdeleGroup.ideleModule ℚ b).2.le (by positivity)
        _ = _ := by ring
    refine h1.trans (le_trans ?_ (real_step (max C 0) _ _ (B * B) T d N hA hP (le_max_right _ _)
      (by positivity) hle))
    gcongr
    exact le_max_left _ _

end GlobalTheory.CompanionTheory.GaugeSpan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegral
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Abstract

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem fubini_unimod {dy : Measure Y} {dx : Measure X} [SFinite dy] [SFinite dx] {f : Y → ℂ} {g : X → ℂ}
    (hf : Integrable f dy) (hg : Integrable g dx) {u : Y → X → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (dy.prod dx)) (hn : ∀ y x, ‖u y x‖ = 1) :
    ∫ y, f y * ∫ x, g x * u y x ∂dx ∂dy = ∫ x, g x * ∫ y, f y * u y x ∂dy ∂dx := by
  have h0 : Integrable (fun z : Y × X => f z.1 * g z.2) (dy.prod dx) := hf.mul_prod hg
  have hint : Integrable (Function.uncurry fun y x => f y * (g x * u y x)) (dy.prod dx) := by
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (h0.aestronglyMeasurable.mul hu).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hn, mul_one, le_refl]
  have hL : ∀ y, f y * ∫ x, g x * u y x ∂dx = ∫ x, f y * (g x * u y x) ∂dx := fun y =>
    (integral_const_mul _ _).symm
  have hR : ∀ x, g x * ∫ y, f y * u y x ∂dy = ∫ y, f y * (g x * u y x) ∂dy := fun x => by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

end Abstract

section Pair

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem pairHerm_sub (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S A B : HermR R σ n) :
    pairHerm R σ n S (A - B) = pairHerm R σ n S A - pairHerm R σ n S B := by
  simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]

theorem half_trace_mul_eq_pairHerm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem half_trace_mul_eq_pairHerm' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  rw [Matrix.trace_mul_comm]
  exact half_trace_mul_eq_pairHerm R σ S G

theorem continuous_pairHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F E] (σ : E →ₐ[F] E) (n : ℕ) :
    Continuous fun z : HermR R σ n × HermR R σ n => pairHerm R σ n z.1 z.2 := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing R
  unfold pairHerm
  refine continuous_const.mul ((GlobalTheory.CompanionTheory.SW.TopK.continuous_trace R).comp ?_)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem b a)

end Pair

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_pairHerm_gramH_sub (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hg : Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) (c : HermR R σ n) :
    Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2 - c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp := continuous_pairHerm (F := F) (E := E) R σ n
  have hgH : Continuous fun x : Fin n → Fin M → R ⊗[F] E => gramH hCM hJ R x :=
    Continuous.subtype_mk hg _
  have m1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, gramH hCM hJ R z.2) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst (hgH.comp continuous_snd)
  have m2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, c) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst continuous_const
  have h1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2) := by
    have h := hp.comp m1
    exact h
  have h2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) => pairHerm R σ n z.1 c := by
    have h := hp.comp m2
    exact h
  have := h1.sub h2
  refine this.congr fun z => ?_
  exact (pairHerm_sub R σ z.1 _ c).symm

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chiT_eq (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c) (y : HermR (AF F) σ n) :
    chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := by
  rw [← half_trace_mul_eq_pairHerm' (AF F) σ y (hermOf (AF F) σ T hT)]
  rfl

theorem psi_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x))) * chiT σ ψ T y =
    ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) := by
  have h2 : algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) :=
    half_trace_mul_eq_pairHerm (AF F) σ y (gramH hCM hJ (AF F) x)
  rw [h2, chiT_eq σ ψ T hT, ← AddChar.map_add_eq_mul, pairHerm_sub, sub_eq_add_neg]

theorem starN_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) :
    GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y =
      ∫ x, Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := by
  rw [GlobalTheory.CompanionTheory.SiegelND.starN, ← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, psi_mul_chiT hCM hJ ψ T hT]

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN_fouH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ M J hJ n hCM ψ hψ dx db _ _ Φ hΦ τ hTh hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hψc, hψn, -⟩ := hψ
  have hpc := continuous_pairHerm_gramH_sub (AF F) hCM hJ (hg n M J) (hermOf (AF F) σ T hT)
  refine ⟨?_, ?_⟩
  · have hp := continuous_pairHerm (F := F) (E := E) (AF F) σ n
    have m : Continuous fun y : HermR (AF F) σ n =>
        ((y, hermOf (AF F) σ T hT) : HermR (AF F) σ n × HermR (AF F) σ n) :=
      Continuous.prodMk continuous_id continuous_const
    have h1 := (hp.comp m).neg
    have h2 := hψc.comp h1
    have : GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T =
        fun y => ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := funext (chiT_eq σ ψ T hT)
    rw [this]
    exact h2
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (y : HermR (AF F) σ n)
        (x : Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT))) (db.prod dx) :=
      (hψc.comp hpc).aestronglyMeasurable
    have key := fubini_unimod hTh hΦ hmeas (fun y x => hψn _)
    have hL : ∀ y, fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) =
        fouH σ ψ db τ y * ∫ x, Φ x *
          ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := fun y => by
      rw [starN_mul_chiT hCM hJ ψ dx Φ T hT y]
    have hR : ∀ x, ∫ y, fouH σ ψ db τ y *
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂db =
        τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) := fun x => by
      rw [hinv, neg_sub]
    simp_rw [hL]
    rw [key]
    simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumConjugation
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

theorem GS_eq_sum_zmod (d : ℕ) [NeZero d] (r : ℤ) :
    GS r d = ∑ y : ZMod d, ZMod.stdAddChar ((r : ZMod d) * y ^ 2) := by
  unfold GS
  refine Finset.sum_nbij' (fun x : ℕ => (x : ZMod d)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro y _; simpa using ZMod.val_lt y
  · intro x hx; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hx)
  · intro y _; simp
  · intro x _
    have hc : ((r : ZMod d) * (x : ZMod d) ^ 2) = ((r * (x : ℤ) ^ 2 : ℤ) : ZMod d) := by
      push_cast; ring
    rw [hc, ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring

theorem gauss_sum_conjugation : T4 := by
  intro M d a b c' hd h
  have : NeZero d := ⟨hd.ne'⟩
  have h1 : (-(b : ZMod d)) * (4 * (M : ZMod d) ^ 2 * (c' : ZMod d)) = 1 := by
    have h2 := congrArg (Int.cast : ℤ → ZMod d) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    linear_combination h2
  let u : (ZMod d)ˣ :=
    ⟨2 * (M : ZMod d) * (c' : ZMod d), -(b : ZMod d) * 2 * (M : ZMod d),
      by linear_combination h1, by linear_combination h1⟩
  rw [GS_eq_sum_zmod, GS_eq_sum_zmod, map_sum,
    ← Equiv.sum_comp (Units.mulLeft u) (fun y : ZMod d =>
      (starRingEnd ℂ) (ZMod.stdAddChar ((b : ZMod d) * y ^ 2)))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp only [Units.mulLeft_apply, u]
  linear_combination ((c' : ZMod d) * y ^ 2) * h1

end GlobalTheory.CompanionTheory.HalfWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitian
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram

theorem inner_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  intro D θ hθ V r ρ
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · change Continuous (fun y : Mx D V.rank r => GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y))
    exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  · change GlobalTheory.MixModel.adj (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)) = GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)
    rw [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  · change compAt θ ρ (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram V) * y)) = _
    rw [GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_adj hθ, GlobalTheory.CompanionTheory.WSum.compAt_rat hθ, Matrix.mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_norm_one_product : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL E a)) [ν.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Measure.map (fun p : GroundTheory.Automorphic.Reduction.normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | exact GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | (intros; apply GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumSquareCoefficientLocalSeries
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.LocalSeries

theorem good_prime_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  intro hE2a hE2b k N χ a hEig hk p hp α β y s hα hβ hsum hprod hr hy hs
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : 0 < p := hp.pos
  set c : ℂ := χ p with hc
  set P : ℂ := (p : ℂ) ^ (k - 1) with hP
  have hcP : c * P ≠ 0 := by rw [← hprod]; exact mul_ne_zero hα hβ
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcP
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hcP

  have hX : ‖y * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : (p : ℝ) ^ (-s).re < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast hp.one_lt
      · simpa using hs
    have h2 : 0 ≤ (p : ℝ) ^ (-s).re := by positivity
    calc ‖y‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ < 1 := by simpa using h1

  have hpow : (p : ℂ) ^ (-(s + k - 1)) = (p : ℂ) ^ (-s) * P⁻¹ := by
    have hk1 : ((k : ℂ) - 1) = ((k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub hk]; simp
    have : -(s + k - 1) = -s + -(((k - 1 : ℕ) : ℂ)) := by
      rw [← hk1]; ring
    rw [this, Complex.cpow_add _ _ hp0, Complex.cpow_neg (p : ℂ) ((k - 1 : ℕ) : ℂ), Complex.cpow_natCast]
  have hmain := hE2b (α / β) (y * (p : ℂ) ^ (-s)) hr hX
  have hinv : c⁻¹ * β ^ 2 * P⁻¹ = (α / β)⁻¹ := by
    have h1 : c⁻¹ * P⁻¹ = (α * β)⁻¹ := by rw [hprod, mul_inv]
    calc c⁻¹ * β ^ 2 * P⁻¹ = (c⁻¹ * P⁻¹) * β ^ 2 := by ring
      _ = (α / β)⁻¹ := by rw [h1]; field_simp
  have hterm : ∀ j : ℕ, c⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j =
      (∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i) * ((α / β)⁻¹ * (y * (p : ℂ) ^ (-s))) ^ j := by
    intro j
    have hcoef : a (p ^ (2 * j)) = β ^ (2 * j) * ∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i := by
      rw [(hE2a k N χ a hEig).2 p hp α β hsum hprod (2 * j), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ 2 * j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hb : β ^ (2 * j) = β ^ (2 * j - i) * β ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hi']
      rw [hb, div_pow]
      field_simp
    rw [hcoef, hpow, ← hinv, pow_mul β 2 j]
    simp only [mul_pow]
    ring
  rw [funext hterm]
  exact hmain

end GlobalTheory.CompanionTheory.LocalSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFiniteStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_haar_splits_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (n : ℕ) (db : Measure (HermR (AF F) σ n)), db.IsAddHaarMeasure →
  ∃ (ν₁ : Measure (HermR (Ainf F) σ n)) (ν₂ : Measure (HermR (Af F) σ n)) (c : ℝ≥0∞),
    ν₁.IsAddHaarMeasure ∧ ν₂.IsAddHaarMeasure ∧ SFinite ν₁ ∧ SFinite ν₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun b : HermR (AF F) σ n => (hermInf σ b, hermFin σ b)) ∧
    db.map (fun b => (hermInf σ b, hermFin σ b)) = c • ν₁.prod ν₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod <;> assumption)
end

