import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsDoubleCoset
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Imports
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LatticePointsBelowFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (La : AddSubgroup W) (g : archUnitary h v) (t : ℝ), IsLattice E La →
    {x : W | x ∈ La ∧ M.len (invApply g (vecAt v x)) < t}.Finite

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_injective (h : HermitianForm F E W) (v : Basis ι E W) :
    Function.Injective (archEmbed h v) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have h1 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E).map w.embedding = 1 :=
    congrArg
      (fun g : archUnitary h v => (((g : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) : Matrix ι ι ℂ)) hγ
  have h2 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) = 1 := by
    ext i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at this
    apply w.embedding.injective
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : unitaryGroupEquivMatrix h v γ = 1 := Subtype.ext (Units.ext h2)
  rwa [MulEquiv.map_eq_one_iff] at h3

theorem countable_unitaryGroup (h : HermitianForm F E W) (v : Basis ι E W) :
    Countable h.unitaryGroup := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix ι ι E) := inferInstanceAs (Countable (ι → ι → E))
  refine Function.Injective.countable (f := fun γ : h.unitaryGroup =>
    ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E)) ?_
  intro a b hab
  exact (unitaryGroupEquivMatrix h v).injective (Subtype.ext (Units.ext hab))

theorem AdelicCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by
  classical
  intro μ _
  obtain ⟨ψ, hψ⟩ := h₃
  obtain ⟨K, D, L, hKc, hKo, hLD, hLeq, hLinj⟩ := h₄
  let e : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
      unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      archUnitary h v × unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
    { toMulEquiv := MulEquiv.prodCongr ψ.toMulEquiv (MulEquiv.refl _)
      continuous_toFun := (ψ.continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd }
  let Φ := (adeleSplit h v).trans e
  have hΦ₁ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).1 = archEmbed h v γ :=
    fun γ => hψ γ
  have hΦ₂ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).2 =
      (adeleSplit h v (hermitianDiagonal h v γ)).2 := fun γ => rfl
  haveI := countable_unitaryGroup h v
  haveI : Countable (hermitianDiagonal h v).range := by
    refine Function.Surjective.countable (f := fun γ : h.unitaryGroup =>
      (⟨hermitianDiagonal h v γ, γ, rfl⟩ : (hermitianDiagonal h v).range)) ?_
    rintro ⟨_, γ, rfl⟩
    exact ⟨γ, rfl⟩

  obtain ⟨S₀, hS₀, hS₀cov⟩ := h₁ D
  let r : AddSubgroup W → unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) := fun L₀ => if hL : ∃ y, L y = L₀ then hL.choose else 1
  have hr : ∀ y, L (r (L y)) = L y := fun y => by
    have hL : ∃ y', L y' = L y := ⟨y, rfl⟩
    simp only [r, dif_pos hL]
    exact hL.choose_spec

  have hstab : ∀ (γ : h.unitaryGroup) (s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F)),
      γ ∈ latticeStab h (L s) ↔ s⁻¹ * (Φ (hermitianDiagonal h v γ)).2 * s ∈ K := by
    intro γ s
    rw [latticeStab, MulAction.mem_stabilizer_iff, hΦ₂, ← hLeq, eq_comm, hLinj, mul_assoc]
  have hslice : ∀ s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F), sliceGroup Φ (hermitianDiagonal h v).range K s =
      archLatticeGroup h v (L s) := by
    intro s
    ext x
    rw [mem_sliceGroup, archLatticeGroup, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨γ, rfl⟩, hk, rfl⟩
      exact ⟨γ, (hstab γ s).2 hk, (hΦ₁ γ).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hermitianDiagonal h v γ, ⟨γ, rfl⟩, (hstab γ s).1 hγ, hΦ₁ γ⟩
  obtain ⟨FD, hFD, hfin⟩ := h₅ Φ (hermitianDiagonal h v).range K (hS₀.toFinset.image r) hKc hKo
    (by
      rintro _ ⟨γ, rfl⟩ h1
      rw [hΦ₁, ← (archEmbed h v).map_one] at h1
      rw [archEmbed_injective h v h1, map_one])
    (by
      intro y
      obtain ⟨L₀, hL₀, g, hg⟩ := hS₀cov (L y) (hLD y)
      have hL₀' : L₀ = L ((adeleSplit h v (hermitianDiagonal h v g⁻¹)).2 * y) := by
        rw [hLeq, ← hg, smul_smul, inv_mul_cancel, one_smul]
      have hs : L (r L₀) = L₀ := by rw [hL₀']; exact hr _
      have hk : ((Φ (hermitianDiagonal h v g)).2 * r L₀)⁻¹ * y ∈ K := by
        rw [← hLinj, hΦ₂, hLeq, hs, hg]
      refine ⟨hermitianDiagonal h v g, ⟨g, rfl⟩, r L₀, ?_, _, hk, ?_⟩
      · exact Finset.mem_image_of_mem r (hS₀.mem_toFinset.2 hL₀)
      · group)
    (by
      intro s _ μ₁ _
      rw [hslice s]
      exact h₂ μ₁ D (L s) (hLD s))
    μ
  exact ⟨FD, hFD, hfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise

noncomputable section

theorem eq_zero_of_isIntegral_of_forall_place_lt_one {K : Type*} [Field K] [NumberField K] {c : K}
    (hc : IsIntegral ℤ c) (hlt : ∀ w : InfinitePlace K, w c < 1) : c = 0 := by
  by_contra hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have ha : (⟨c, hc⟩ : 𝓞 K) ≠ 0 := fun h0 => hne (congrArg ((↑) : 𝓞 K → K) h0)
  exact absurd (InfinitePlace.one_le_of_lt_one ha (fun z _ => hlt z)) (not_le.2 (hlt w))

section Discrete

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_apply_val (h : HermitianForm F E W) (v : Basis ι E W) (g : h.unitaryGroup)
    (w : InfinitePlace E) :
    ((((archEmbed h v g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) :
        Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

theorem ArchLatticeDiscrete.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchLatticeDiscrete.Statement h v := by
  classical
  intro La hLa
  obtain ⟨S, hS⟩ := hLa.fg
  have hSLa : ∀ s ∈ S, s ∈ La := fun s hs => hS ▸ AddSubgroup.subset_closure hs

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add, Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    rw [← hS, AddSubgroup.closure_le]
    intro s hs i
    exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  have key : ∀ y ∈ La, (∀ (w : InfinitePlace E) (i : ι),
      |(d : ℝ)| * ‖w.embedding (v.repr y i)‖ < 1) → y = 0 := by
    intro y hy hsmall
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have hz := eq_zero_of_isIntegral_of_forall_place_lt_one (hLaT hy i) fun w => by
      rw [← InfinitePlace.norm_embedding_eq, zsmul_eq_mul, map_mul, map_intCast, norm_mul,
        Complex.norm_intCast]
      exact hsmall w i
    rw [zsmul_eq_mul] at hz
    simpa [hdE] using hz

  set B : ℝ := ∑ s ∈ S, ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdpos : 0 < |(d : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd0)
  set δ : ℝ := 1 / (|(d : ℝ)| * (B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hdδB : |(d : ℝ)| * δ * B < 1 := by
    have e : |(d : ℝ)| * δ = 1 / (B + 1) := by
      rw [hδ]; field_simp
    rw [e, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  let U : Set (InfinitePlace E → GL ι ℂ) :=
    {g | ∀ w i j, ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}
  have hU : IsOpen U := by
    have e : U = ⋂ w, ⋂ i, ⋂ j, {g : InfinitePlace E → GL ι ℂ |
        ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ} := by
      ext g; simp [U]
    rw [e]
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact (((Units.continuous_val.comp (continuous_apply w)).matrix_elem i j).sub
      continuous_const).norm

  have hone : ∀ γ ∈ latticeStab h La,
      ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) ∈ U → γ = 1 := by
    intro γ hγ hγU
    set M := LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) with hM
    have hγLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x ∈ La := by
      intro x hx
      have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul x γ La hx
      rwa [MulAction.mem_stabilizer_iff.1 hγ] at h1
    have hrep : ∀ x : W, ∀ i, v.repr ((γ : W ≃ₗ[E] W) x - x) i =
        ∑ j, (M i j - (1 : Matrix ι ι E) i j) * v.repr x j := by
      intro x i
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i
      simp only [LinearEquiv.coe_coe] at h1
      rw [map_sub, Finsupp.sub_apply, ← h1]
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hM]
    have h1ij : ∀ (w : InfinitePlace E) i j,
        w.embedding ((1 : Matrix ι ι E) i j) = (1 : Matrix ι ι ℂ) i j := by
      intro w i j
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hfix : ∀ s ∈ S, (γ : W ≃ₗ[E] W) s = s := by
      intro s hs
      refine sub_eq_zero.1 (key _ (sub_mem (hγLa s (hSLa s hs)) (hSLa s hs)) fun w i => ?_)
      have entry : ∀ j, ‖w.embedding (M i j - (1 : Matrix ι ι E) i j)‖ < δ := by
        intro j
        have := hγU w i j
        rw [archEmbed_apply_val, Matrix.map_apply] at this
        rwa [map_sub, h1ij]
      have hsum : ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖ ≤
          δ * ∑ j, ‖w.embedding (v.repr s j)‖ := by
        rw [hrep, map_sum, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (entry j).le (norm_nonneg _)
      have hsB : ∑ j, ‖w.embedding (v.repr s j)‖ ≤ B := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ w : InfinitePlace E, ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) hs)
        exact Finset.single_le_sum (f := fun w : InfinitePlace E => ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)
      calc |(d : ℝ)| * ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖
          ≤ |(d : ℝ)| * (δ * B) := by
            gcongr
            exact hsum.trans (mul_le_mul_of_nonneg_left hsB hδpos.le)
        _ = |(d : ℝ)| * δ * B := by ring
        _ < 1 := hdδB
    have hfixLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x = x := by
      intro x hx
      rw [← hS] at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx => exact hfix x hx
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | neg x _ hx => simp [map_neg, hx]
    have hlin : ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) = LinearMap.id :=
      LinearMap.ext_on hLa.span_eq_top fun x hx => hfixLa x hx
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simpa using LinearMap.congr_fun hlin x

  refine discreteTopology_of_isOpen_singleton_one ?_
  have hcont : Continuous fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have e : ({1} : Set (archLatticeGroup h v La)) = (fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)) ⁻¹' U := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl w i j
      simpa using hδpos
    · intro hx
      obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 x.2
      have h1 := hone γ hγ (by rw [hγx]; exact hx)
      apply Subtype.ext
      rw [← hγx, h1, map_one]
      rfl
  rw [e]
  exact hU.preimage hcont

end Discrete

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoeffLatticeBasis
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Set Topology

theorem DiscreteFundamentalDomain.proof (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G := by
  classical
  intro μ Γ hΓ

  have hcount : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1t : (1 : G) ∈ t := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' t := by rw [hteq]; rfl
    simpa using this

  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_split (ht.mem_nhds h1t)
  let U : Set G := V ∩ V⁻¹
  have hUo : IsOpen U := hVo.inter hVo.inv
  have hU1 : (1 : G) ∈ U := ⟨hV1, by simpa using hV1⟩
  have key : ∀ u ∈ U, ∀ w ∈ U, ∀ γ : Γ, (γ : G) = u * w⁻¹ → γ = 1 := by
    intro u hu w hw γ hγ
    have h : (γ : G) ∈ t := hγ ▸ hVV u hu.1 w⁻¹ hw.2
    have h' : γ ∈ ((↑) : Γ → G) ⁻¹' t := h
    rw [hteq] at h'
    exact h'

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : G => (fun x => x * g⁻¹) ⁻¹' U) (fun g => hUo.preimage (continuous_mul_const _))
  have hall : ∀ x : G, x ∈ ⋃ g : G, (fun x => x * g⁻¹) ⁻¹' U := fun x =>
    mem_iUnion.2 ⟨x, by simpa using hU1⟩
  have hTne : T.Nonempty := by
    have h := hall 1
    rw [← hTU] at h
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 h
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hTc.exists_eq_range hTne
  let A : ℕ → Set G := fun n => (fun x => x * (g n)⁻¹) ⁻¹' U
  have hAo : ∀ n, IsOpen (A n) := fun n => hUo.preimage (continuous_mul_const _)
  have hcover : ∀ x : G, ∃ n, x ∈ A n := by
    intro x
    have h := hall x
    rw [← hTU, hg] at h
    obtain ⟨_, ⟨n, rfl⟩, hx⟩ := mem_iUnion₂.1 h
    exact ⟨n, hx⟩

  let FD : Set G :=
    ⋃ n, A n ∩ ⋂ m, ⋂ (_ : m < n), ⋂ γ : Γ, (fun x => (γ : G) * x) ⁻¹' (A m)ᶜ
  have memFD : ∀ y, y ∈ FD ↔ ∃ n, y ∈ A n ∧ ∀ m < n, ∀ γ : Γ, (γ : G) * y ∉ A m := by
    intro y
    simp only [FD, mem_iUnion, mem_inter_iff, mem_iInter, mem_preimage, mem_compl_iff]
  have hmeas : MeasurableSet FD :=
    MeasurableSet.iUnion fun n => (hAo n).measurableSet.inter <|
      MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun γ =>
        (hAo m).measurableSet.compl.preimage (continuous_const_mul _).measurable

  have uniq : ∀ y, ∀ δ : Γ, y ∈ FD → (δ : G) * y ∈ FD → δ = 1 := by
    intro y δ hy hδy
    obtain ⟨n₁, hy₁, hy₂⟩ := (memFD y).1 hy
    obtain ⟨n₂, hδ₁, hδ₂⟩ := (memFD _).1 hδy
    rcases lt_trichotomy n₁ n₂ with h | rfl | h
    · exact absurd (by simpa using hy₁) (hδ₂ n₁ h δ⁻¹)
    · refine key _ hδ₁ _ hy₁ δ ?_
      group
    · exact absurd hδ₁ (hy₂ n₂ h δ)
  refine ⟨FD, hmeas, IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_⟩

  have hP : ∃ n, ∃ γ : Γ, (γ : G) * x ∈ A n := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, 1, by simpa using hn⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  have hγFD : (γ : G) * x ∈ FD := by
    refine (memFD _).2 ⟨Nat.find hP, hγ, fun m hm δ hδ => Nat.find_min hP hm ⟨δ * γ, ?_⟩⟩
    simpa [mul_assoc] using hδ
  refine ⟨γ, by simpa [Subgroup.smul_def] using hγFD, fun δ hδ => ?_⟩
  have hδ' : (δ : G) * x ∈ FD := by simpa [Subgroup.smul_def] using hδ
  have h1 := uniq _ (δ * γ⁻¹) hγFD (by simpa [mul_assoc] using hδ')
  simpa [mul_inv_eq_one] using h1

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

