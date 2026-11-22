import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_smul_eq_of_eigvec_of_charpoly_separable {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g.charpoly.Separable) {μ : ℂ} {x y : Fin n → ℂ} (hx0 : x ≠ 0)
    (hx : g *ᵥ x = μ • x) (hy : g *ᵥ y = μ • y) : ∃ c : ℂ, y = c • x := by
  set f := Matrix.toLin' g
  have hc : f.charpoly = g.charpoly := Matrix.charpoly_toLin' g
  have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, hc]
    exact Polynomial.rootMultiplicity_le_one_of_separable hg μ
  have mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ := fun v hv => by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp [f, hv]⟩
  have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
    (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ)
    fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem form_conjTranspose_mul_mul {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ (gᴴ * A * g) *ᵥ v = star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eigvec_pos_unique_of_similitude : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    A.det ≠ 0 → sigPosH hA = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s →
    gᴴ * A * g = (s : ℂ) • A → g.charpoly.Separable → ∀ x y : Fin n → ℂ,
    0 < (star x ⬝ᵥ A *ᵥ x).re → 0 < (star y ⬝ᵥ A *ᵥ y).re →
    (∃ μ : ℂ, g *ᵥ x = μ • x) → (∃ ν : ℂ, g *ᵥ y = ν • y) → ∃ c : ℂ, y = c • x := by
  intro n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxp
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyp
  have Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v) := by
    intro u v
    rw [← form_conjTranspose_mul_mul, hsim]
    have e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v) := by
      exact Matrix.smul_mulVec (s : ℂ) A v
    rw [e, dotProduct_smul, smul_eq_mul]
  have scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v) := by
    intro a b u v
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hxp; simp at hxp
  have hQy : star y ⬝ᵥ A *ᵥ y ≠ 0 := fun h => by rw [h] at hyp; simp at hyp
  have eμ : star μ * μ = (s : ℂ) := by
    have := Q x x; rw [hμ, scal] at this; exact mul_right_cancel₀ hQx this
  have eν : star ν * ν = (s : ℂ) := by
    have := Q y y; rw [hν, scal] at this; exact mul_right_cancel₀ hQy this
  have exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0 := by
    have := Q x y; rw [hμ, hν, scal] at this; rw [sub_mul, this, sub_self]
  by_cases hμν : μ = ν
  · subst hμν
    exact exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν
  · exfalso
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hμ0 : star μ ≠ 0 := fun h => hs0 (by rw [← eμ, h, zero_mul])
    have hne : star μ * ν - s ≠ 0 := by
      intro h
      apply hμν
      have : star μ * ν = star μ * μ := by rw [eμ]; exact sub_eq_zero.1 h
      exact (mul_left_cancel₀ hμ0 this).symm
    have horth : star x ⬝ᵥ A *ᵥ y = 0 := (mul_eq_zero.1 exy).resolve_left hne
    have := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.CoordArch

variable {p : ℕ} [Fact p.Prime]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_infinitePlace_embedding (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] (w : InfinitePlace K → ℂ) :
    w ∈ Submodule.span ℝ (Set.range fun (f : K) (u : InfinitePlace K) => u.embedding f) := by
  have hc : ∀ u : InfinitePlace K, u.IsComplex := fun u => IsTotallyComplex.isComplex u
  let P : mixedEmbedding.mixedSpace K →ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun x u => x.2 ⟨u, hc u⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : ∀ f : K, P (mixedEmbedding K f) = fun u => u.embedding f := by
    intro f; funext u
    exact mixedEmbedding.mixedEmbedding_apply_isComplex K f ⟨u, hc u⟩
  have hmem : ((0, fun u => w u.1) : mixedEmbedding.mixedSpace K) ∈
      Submodule.span ℝ (Set.range (mixedEmbedding.latticeBasis K)) := by
    rw [(mixedEmbedding.latticeBasis K).span_eq]; trivial
  have hmap := Submodule.mem_map_of_mem (f := P) hmem
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨_, (by rw [mixedEmbedding.latticeBasis_apply, hP])⟩

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_range_psi {p : ℕ} [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p)
    (v : InfinitePlace G.F) (M : Matrix (Fin G.n) (Fin G.n) ℂ) :
    M ∈ Submodule.span ℂ (Set.range (G.psi v)) := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hsc : ∀ f : G.F, algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) f =
      Matrix.scalar (Fin G.n) (v.embedding f) := by
    intro f; ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      RingHom.algebraMap_toAlgebra]
  let ψ : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun f => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [G.psi_F, hsc] }
  let φ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ (fun z c => Algebra.commutes z _)
  have hφ : ∀ (z : ℂ) (c : G.C), φ (z ⊗ₜ c) = z • G.psi v c := by
    intro z c
    change (Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ _) (z ⊗ₜ[G.F] c) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
  have hn : 0 < G.n := G.n_pos
  have hinj : Function.Injective φ := by
    let χ : G.C ⊗[G.F] ℂ →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
      φ.toRingHom.comp (Algebra.TensorProduct.comm G.F G.C ℂ).toRingEquiv.toRingHom
    have hker : TwoSidedIdeal.ker χ = ⊥ := by
      by_contra h
      obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot (TwoSidedIdeal.ker χ) h
      rw [TwoSidedIdeal.mem_ker] at hmem
      have h1 : χ (1 ⊗ₜ b) = b • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
        change φ ((Algebra.TensorProduct.comm G.F G.C ℂ) (1 ⊗ₜ b)) = _
        rw [Algebra.TensorProduct.comm_tmul, hφ, map_one]
      rw [hmem] at h1
      have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
      simp at h2
      exact hb h2.symm
    have hχ : Function.Injective χ := (TwoSidedIdeal.ker_eq_bot χ).1 hker
    intro x y hxy
    apply (Algebra.TensorProduct.comm G.F G.C ℂ).symm.injective
    apply hχ
    simpa [χ] using hxy
  have hrank : Module.finrank ℂ (ℂ ⊗[G.F] G.C) =
      Module.finrank ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, G.rankC, Module.finrank_matrix,
      Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  obtain ⟨t, rfl⟩ := hsurj M
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z c =>
    change φ (z ⊗ₜ c) ∈ _
    rw [hφ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in

theorem _root_.GlobalTheory.CoordArch.coord_bound : ∀ (p : ℕ) [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p), ∃ R : ℝ, ∀ (c : G.C) (i : Fin (Module.finrank ℚ G.C)),
    |((Module.finBasis ℚ G.C).repr c i : ℝ)| ≤ R * ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, ‖G.psi w c a b‖ := by
  intro p _ G
  classical
  let B := Module.finBasis ℚ G.C
  let Φ : G.C → (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := fun c u => G.psi u c
  let L : (Fin (Module.finrank ℚ G.C) → ℝ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    Fintype.linearCombination ℝ (fun i => Φ (B i))
  have hL : ∀ c : G.C, L (fun i => (B.repr c i : ℝ)) = Φ c := by
    intro c
    funext u a b
    have h := congrArg (fun x => G.psi u x a b) (B.sum_repr c)
    simp only [map_sum, Matrix.sum_apply, map_rat_smul] at h
    simp only [L, Φ, Fintype.linearCombination_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.smul_def]
  have hF : ∀ (w : InfinitePlace G.F → ℂ) (c : G.C),
      (fun u => w u • G.psi u c) ∈ Submodule.span ℝ (Set.range Φ) := by
    intro w c
    have hw := mem_span_infinitePlace_embedding G.F w
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      refine Submodule.subset_span ⟨algebraMap G.F G.C f * c, ?_⟩
      funext u
      simp only [Φ, map_mul, G.psi_F]
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    | zero =>
      convert Submodule.zero_mem (Submodule.span ℝ (Set.range Φ)) using 1
      funext u
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext u
      simp [add_smul]
    | smul r x _ hx =>
      convert Submodule.smul_mem _ r hx using 1
      funext u
      simp only [Pi.smul_apply]
      exact smul_assoc _ _ _
  have hspan : ∀ y : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ,
      y ∈ Submodule.span ℝ (Set.range Φ) := by
    intro y
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun u _ => ?_
    suffices h : ∀ M ∈ Submodule.span ℂ (Set.range (G.psi u)), ∀ z : ℂ,
        Pi.single u (z • M) ∈ Submodule.span ℝ (Set.range Φ) by
      simpa using h _ (mem_span_range_psi G u (y u)) 1
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      intro z
      convert hF (Pi.single u z) c using 1
      funext u'
      by_cases h : u' = u
      · subst h; simp
      · simp [h]
    | zero =>
      intro z
      rw [smul_zero, Pi.single_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro z
      rw [smul_add, Pi.single_add]
      exact Submodule.add_mem _ (hx z) (hy z)
    | smul z' x _ hx =>
      intro z
      rw [smul_smul]
      exact hx _
  have hrange : LinearMap.range L = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    refine Submodule.span_le.mpr ?_ (hspan y)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, hL c⟩
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℚ G.C) → ℝ) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank G.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces G.F
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero G.F
    have h4 := Module.finrank_mul_finrank ℚ G.F G.C
    have h5 := G.rankC
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← h4, h5, ← h1, h2, h3]
    ring
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
      (LinearMap.range_eq_top.1 hrange)
  let E : (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) ≃ₗ[ℝ]
      (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    LinearEquiv.piCongrRight fun _ => (Matrix.ofLinearEquiv ℝ).symm
  obtain ⟨K, -, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (E.toLinearMap ∘ₗ L)).1 (E.injective.comp hinj)
  refine ⟨K, fun c i => ?_⟩
  have hx := hK.le_mul_dist (fun j => (B.repr c j : ℝ)) 0
  rw [dist_zero_right, map_zero, dist_zero_right] at hx
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hL] at hx
  rw [← Real.norm_eq_abs]
  refine (norm_le_pi_norm (fun j => (B.repr c j : ℝ)) i).trans (hx.trans ?_)
  gcongr
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun u => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  exact (Finset.single_le_sum (f := fun b => ‖G.psi u c a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans ((Finset.single_le_sum (f := fun a => ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ a)).trans
    (Finset.single_le_sum (f := fun u => ∑ a, ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ u)))

end GlobalTheory.CoordArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SchwartzBox

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ ⊕ κ' → V) :
    ‖x‖ ≤ max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i => exact le_max_of_le_left (norm_le_pi_norm (x ∘ Sum.inl) i)
  | inr i => exact le_max_of_le_right (norm_le_pi_norm (x ∘ Sum.inr) i)

def restr (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ → ι) :
    (ι → V) →L[ℝ] (κ → V) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) (e i)

theorem restr_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (x : ι → V) : restr V e x = x ∘ e := rfl

theorem norm_restr_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) : ‖restr V e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => norm_le_pi_norm x (e i)

theorem norm_iteratedFDeriv_restr_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι]
    [Fintype κ] (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (i : ℕ) (x : ι → V) :
    ‖iteratedFDeriv ℝ i (fun y => f (y ∘ e)) x‖ ≤ ‖iteratedFDeriv ℝ i f (x ∘ e)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (restr V e) (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (y ∘ e)) = (f ∘ restr V e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (restr V e x)‖ * ∏ _j : Fin i, ‖restr V e‖
      ≤ ‖iteratedFDeriv ℝ i f (restr V e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_restr_le V e
    _ = _ := mul_one _

theorem exists_schwartz_box {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) :
    ∃ f : SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ x, f x = f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  refine ⟨⟨fun x => f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr), hs₁.mul hs₂, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ k i f₁ * SchwartzMap.seminorm ℝ 0 (n - i) f₂ +
      SchwartzMap.seminorm ℝ 0 i f₁ * SchwartzMap.seminorm ℝ k (n - i) f₂), fun x => ?_⟩
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₁ _ _
        · exact SchwartzMap.le_seminorm ℝ k (n - i) f₂ _

theorem sb_box {X : Type} [TopologicalSpace X] {κ κ' : Type} {g₁ : (κ → X) → ℂ} {g₂ : (κ' → X) → ℂ}
    (hg₁ : g₁ ∈ SB (κ → X)) (hg₂ : g₂ ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  obtain ⟨hl₁, hc₁⟩ := hg₁
  obtain ⟨hl₂, hc₂⟩ := hg₂
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  have he : ∀ z, e z = (z ∘ Sum.inl, z ∘ Sum.inr) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · have c₁ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inl := continuous_pi fun i => continuous_apply _
    have c₂ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inr := continuous_pi fun i => continuous_apply _
    exact (hl₁.comp_continuous c₁).mul (hl₂.comp_continuous c₂)
  · refine HasCompactSupport.intro' (K := e ⁻¹' (tsupport g₁ ×ˢ tsupport g₂))
      (e.isCompact_preimage.2 (hc₁.prod hc₂))
      (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage e.continuous) fun z hz => ?_
    rw [Set.mem_preimage, he, Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

theorem boxFun_zero_left {R κ κ' : Type} (φ : (κ' → R) → ℂ) : boxFun (0 : (κ → R) → ℂ) φ = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_left {R κ κ' : Type} (a b : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (a + b) φ = boxFun a φ + boxFun b φ := by
  funext x; simp [boxFun, add_mul]

theorem boxFun_smul_left {R κ κ' : Type} (c : ℂ) (a : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (c • a) φ = c • boxFun a φ := by
  funext x; simp [boxFun, mul_assoc]

theorem boxFun_zero_right {R κ κ' : Type} (φ : (κ → R) → ℂ) : boxFun φ (0 : (κ' → R) → ℂ) = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_right {R κ κ' : Type} (φ : (κ → R) → ℂ) (a b : (κ' → R) → ℂ) :
    boxFun φ (a + b) = boxFun φ a + boxFun φ b := by
  funext x; simp [boxFun, mul_add]

theorem boxFun_smul_right {R κ κ' : Type} (c : ℂ) (φ : (κ → R) → ℂ) (a : (κ' → R) → ℂ) :
    boxFun φ (c • a) = c • boxFun φ a := by
  funext x; simp [boxFun]; ring

open scoped Classical in

theorem boxFun_mem_schA (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  intro φ₁ h₁ φ₂ h₂
  have gen : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      ∀ Φ₂ ∈ {Φ | ∃ (f : SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
    rintro _ ⟨f₁, g₁, hg₁, rfl⟩ _ ⟨f₂, g₂, hg₂, rfl⟩
    obtain ⟨f, hf⟩ := exists_schwartz_box f₁ f₂
    refine Submodule.subset_span ⟨f, fun z => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr), sb_box hg₁ hg₂, ?_⟩
    funext x
    simp only [boxFun, pureA, hf]
    simp only [Function.comp_def]
    ring
  have gen₂ : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
    intro Φ₁ hΦ₁
    induction h₂ using Submodule.span_induction with
    | mem x hx => exact gen Φ₁ hΦ₁ x hx
    | zero => rw [boxFun_zero_right]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [boxFun_add_right]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [boxFun_smul_right]; exact Submodule.smul_mem _ c hx
  induction h₁ using Submodule.span_induction with
  | mem x hx => exact gen₂ x hx
  | zero => rw [boxFun_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [boxFun_add_left]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [boxFun_smul_left]; exact Submodule.smul_mem _ c hx

end GlobalTheory.SchwartzBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUnitEqZero
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem AddCls.pull_unit_eq_zero {S : Scheme.{0}} {A T Z : Over S} [GrpObj A] {c : Pic (A ⊗ T).left}
    (h : AddCls A c) (t : Z ⟶ T) : CechPic.pull (lift (1 : Z ⟶ A) t).left c = 0 := by
  have h1 := h Z 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem addF_separated : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (y y' : (addF A).obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ (addF A).map z.op y = (addF A).map z.op y') → y = y') := by
  intro S A _ hA T y y' h
  refine Subtype.ext (sub_eq_zero.1 (GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A T hA (y.1 - y'.1) ?_ fun p ↦ ?_))
  · rw [map_sub, y.2.pull_unit_eq_zero, y'.2.pull_unit_eq_zero, sub_zero]
  · obtain ⟨Z, z, hz, hp, e⟩ := h p
    refine ⟨Z, z, hz, hp, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val e

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingWordSpanStableOfLoweringKillStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raisingWordSpan_stable_of_lowering_kill : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  first | exact @GlobalTheory.HolDS.raisingSpan_stable | exact GlobalTheory.HolDS.raisingSpan_stable | (intros; apply GlobalTheory.HolDS.raisingSpan_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePairStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_representation_of_finite_pair : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  first | exact @GlobalTheory.QuotRegular.exists_isReg | exact GlobalTheory.QuotRegular.exists_isReg | (intros; apply GlobalTheory.QuotRegular.exists_isReg <;> assumption)
end

