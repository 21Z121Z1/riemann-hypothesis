import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSchur

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem mul_star_psi (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a * star (ψ a) = 1 := by
  have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.star_def, Complex.mul_conj', h]
  simp

theorem heisO_rat {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    heisO ψ S T γ f x = ψ (symplO S T x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ x
  rw [← GlobalTheory.WeilVacMove.symplOH_skew] at h
  show ψ (symplOH S T x (ratW T S γ)) * f (x + ratW T S γ) = ψ (symplO S T x (ratW T S γ)) * f x
  rw [add_comm x, h, ← mul_assoc, ← AddChar.map_add_eq_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1]

theorem prod_periodic (hψ : IsStdChar D ψ (-1)) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratW T S γ + x) * star (f' (ratW T S γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOH S T (ratW T S γ) x))

theorem prod_eq (hψ : IsStdChar D ψ (-1)) (M : Module.End ℂ (WO S T → ℂ))
    (hM : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hn : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (x : WO S T) :
    M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hint : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by rw [prod_periodic hψ hf hf' hγ, prod_periodic hψ (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisO ψ S T γ f) x * star (M f' x) - heisO ψ S T γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heisO_rat hf γ.2, heisO_rat (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

theorem schur : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hc hn
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have h2 : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisO, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOH S T x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ (symplOH S T x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunO ψ S T f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), ?_, fun f hf => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn1, div_self (norm_ne_zero_iff.2 hy)]
    · funext x
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchur

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOrthogonalKernelStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_orthogonal_kernel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  first | exact @GlobalTheory.SteepMult.section1_mem_orthogonal_ker | exact GlobalTheory.SteepMult.section1_mem_orthogonal_ker | (intros; apply GlobalTheory.SteepMult.section1_mem_orthogonal_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtension
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory

theorem selfDual_orthogonal_unit_step : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hLfg hLspan hdual k f hfL horth hunit hk
  have alg_inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym (z + z') y, hadd, map_add, ← hsym, ← hsym]
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym (a • z) y, hsmul, map_mul, ← hsym]
  let H1 : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z,
      map_smul' := fun a y => by simp [hsmul] }
  let H2 : V → V →+ K.E := fun y => AddMonoidHom.mk' (fun z => h y z) (hadd2 y)
  have h0l : ∀ z, h 0 z = 0 := fun z => (H1 z).map_zero
  have hsub1 : ∀ a b z, h (a - b) z = h a z - h b z := fun a b z => (H1 z).map_sub a b
  have hsub2 : ∀ y a b, h y (a - b) = h y a - h y b := fun y a b => (H2 y).map_sub a b
  have hsum1 : ∀ (g : Fin k → V) z, h (∑ i, g i) z = ∑ i, h (g i) z :=
    fun g z => map_sum (H1 z) g Finset.univ
  have hsum2 : ∀ (g : Fin k → V) y, h y (∑ i, g i) = ∑ i, h y (g i) :=
    fun g y => map_sum (H2 y) g Finset.univ
  have hsmulO : ∀ (o : K.O) (v : V), (algebraMap K.O K.E o) • v = o • v :=
    fun o v => algebraMap_smul K.E o v
  have hint : ∀ y ∈ L, ∀ z ∈ L, ∃ a : K.O, h y z = algebraMap K.O K.E a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    exact ⟨a, ha.symm⟩
  have hs : ∀ i, h (f i) (f i) ≠ 0 := by
    intro i
    obtain ⟨t, ht, he⟩ := hunit i
    rw [he]
    intro h0
    apply ht.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  let M : Submodule K.O V :=
    { carrier := {y | y ∈ L ∧ ∀ i, h y (f i) = 0}
      add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, fun i => by rw [hadd, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, fun i => h0l (f i)⟩
      smul_mem' := fun o y hy => ⟨L.smul_mem o hy.1, fun i => by rw [← hsmulO, hsmul, hy.2 i, mul_zero]⟩ }
  have memM : ∀ y, y ∈ M ↔ y ∈ L ∧ ∀ i, h y (f i) = 0 := fun y => Iff.rfl

  have hP : ∀ l ∈ L, ∃ p ∈ M, (∀ w, (∀ i, h w (f i) = 0) → h w l = h w p) ∧
      (l ∉ Submodule.span K.E (Set.range f) → p ≠ 0) := by
    intro l hl
    set g : Fin k → V := fun i => (h l (f i) / h (f i) (f i)) • f i with hg
    have hgL : ∀ i, g i ∈ L := by
      intro i
      obtain ⟨a, ha⟩ := hint l hl (f i) (hfL i)
      obtain ⟨t, ht, he⟩ := hunit i
      have hc : h l (f i) / h (f i) (f i) = algebraMap K.O K.E (a * ↑ht.unit⁻¹) := by
        rw [ha, he, map_mul, div_eq_mul_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
      simp only [hg]
      rw [hc, hsmulO]
      exact L.smul_mem _ (hfL i)
    refine ⟨l - ∑ i, g i, (memM _).2 ⟨L.sub_mem hl (L.sum_mem fun i _ => hgL i), fun j => ?_⟩,
      fun w hw => ?_, fun hn h0 => ?_⟩
    · rw [hsub1, hsum1, Finset.sum_eq_single j]
      · simp only [hg, hsmul]
        rw [div_mul_cancel₀ _ (hs j), sub_self]
      · intro i _ hij
        simp only [hg, hsmul, horth i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · rw [hsub2, hsum2, Finset.sum_eq_zero, sub_zero]
      intro i _
      simp only [hg, hsmul2, hw i, mul_zero]
    · apply hn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hspan : Submodule.span K.E (Set.range f) ≠ ⊤ := by
    intro htop
    have h1 := finrank_range_le_card (R := K.E) f
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨l, hl, hlnot⟩ : ∃ l ∈ L, l ∉ Submodule.span K.E (Set.range f) := by
    by_contra hcon
    push_neg at hcon
    apply hspan
    rw [eq_top_iff, ← hLspan]
    exact Submodule.span_le.2 (fun x hx => hcon x hx)
  have hMne : M ≠ ⊥ := by
    obtain ⟨p, hpM, -, hp0⟩ := hP l hl
    intro hb
    rw [hb] at hpM
    exact hp0 hlnot ((Submodule.mem_bot _).1 hpM)

  by_contra hno
  push_neg at hno
  let Q : Submodule K.O K.E := Submodule.map (Algebra.linearMap K.O K.E) (IsLocalRing.maximalIdeal K.O)
  have hQsmul : ∀ (o : K.O) x, x ∈ Q → algebraMap K.O K.E o * x ∈ Q := by
    intro o x hx
    rw [← Algebra.smul_def]
    exact Q.smul_mem o hx
  have hQdiag : ∀ y ∈ M, h y y ∈ Q := by
    intro y hy
    obtain ⟨t, ht⟩ := hint y hy.1 y hy.1
    refine Submodule.mem_map.2 ⟨t, ?_, by rw [Algebra.linearMap_apply, ht]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hno y hy.1 hy.2 t hu ht
  have hpol : ∀ y ∈ M, ∀ z ∈ M, ∀ o : K.O,
      algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z ∈ Q := by
    intro y hy z hz o
    obtain ⟨μ, hμ⟩ := K.c_int o
    have hw : y + (algebraMap K.O K.E o) • z ∈ M := by
      rw [hsmulO]
      exact M.add_mem hy (M.smul_mem o hz)
    have e : algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z =
        h (y + (algebraMap K.O K.E o) • z) (y + (algebraMap K.O K.E o) • z) - h y y
          - algebraMap K.O K.E o * (algebraMap K.O K.E μ * h z z) := by
      simp only [hadd, hadd2, hsmul, hsmul2, hμ]
      ring
    rw [e]
    exact Q.sub_mem (Q.sub_mem (hQdiag _ hw) (hQdiag _ hy)) (hQsmul _ _ (hQsmul _ _ (hQdiag _ hz)))
  have hQall : ∀ y ∈ M, ∀ z ∈ M, h y z ∈ Q := by
    intro y hy z hz
    obtain ⟨a, b, hab, hnot⟩ := K.c_res
    have h1 := hpol y hy z hz 1
    have h2 := hpol y hy z hz a
    simp only [map_one, one_mul] at h1
    rw [hab] at h2
    have h3 : algebraMap K.O K.E (a - b) * h y z ∈ Q := by
      have := Q.sub_mem (hQsmul a _ h1) h2
      convert this using 1
      rw [map_sub]
      ring
    obtain ⟨e, he⟩ := hint y hy.1 z hz.1
    rw [he, ← map_mul] at h3
    obtain ⟨m', hm', hm'e⟩ := Submodule.mem_map.1 h3
    rw [Algebra.linearMap_apply] at hm'e
    have hme := alg_inj hm'e
    rw [hme] at hm'
    rw [he]
    exact Submodule.mem_map.2 ⟨e,
      ((IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hm').resolve_left hnot, rfl⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπm : IsLocalRing.maximalIdeal K.O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπmem : π ∈ IsLocalRing.maximalIdeal K.O := by
    rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  have hle : M ≤ IsLocalRing.maximalIdeal K.O • M := by
    intro w hw
    have hw' : (algebraMap K.O K.E π)⁻¹ • w ∈ M := by
      refine (memM _).2 ⟨(hdual _).2 fun l hl => ?_, fun i => by rw [hsmul, hw.2 i, mul_zero]⟩
      obtain ⟨p, hp, hpw, -⟩ := hP l hl
      rw [hsmul, hpw w hw.2]
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 (hQall w hw p hp)
      rw [hπm, Ideal.mem_span_singleton'] at hb
      obtain ⟨d, rfl⟩ := hb
      rw [← hbe, Algebra.linearMap_apply, map_mul]
      exact ⟨d, by field_simp⟩
    have hweq : w = π • ((algebraMap K.O K.E π)⁻¹ • w) := by
      rw [← hsmulO, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [hweq]
    exact Submodule.smul_mem_smul hπmem hw'
  have hfg : M.FG := Submodule.FG.of_le hLfg (fun y hy => hy.1)
  exact hMne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle
    (IsLocalRing.maximalIdeal_le_jacobson _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.KirArchTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_here : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_map_pInf_here :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_here)

theorem ent {R : Type} [CommRing R] (p : Ad E →+* R) (g : GA E a) (i j : Fin a) :
    ((GeneralLinearGroup.map p g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j = p ((g : Matrix (Fin a) (Fin a) (Ad E)) i j) :=
  rfl

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem eq_finGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E a (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem comm_infGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin a) (Cinf E)) :
    q * infGL E a y = infGL E a y * q := by
  rw [eq_finGL hq]
  exact (infGL_comm y _).symm

theorem infGL_apply_of_ne (y : GL (Fin a) (Cinf E)) {i j : Fin a} (h : i ≠ j) :
    (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) := by
  refine ad_ext ?_ ?_
  · rw [← ent, pInf_infGL, pInf_sInf]
  · rw [← ent, pFin_infGL, pFin_sInf]
    simp [Matrix.one_apply, h]

theorem infGL_mem_NA {u : GL (Fin a) (Cinf E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a)) :
    infGL E a u ∈ GlobalTheory.JSW.NA E a := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · refine ad_ext ?_ ?_
    · rw [map_zero, ← ent, pInf_infGL]; exact h1 i j hji
    · rw [map_zero, ← ent, pFin_infGL]; simp [Matrix.one_apply, hji.ne']
  · refine ad_ext ?_ ?_
    · rw [map_one, ← ent, pInf_infGL]; exact h2 i
    · rw [map_one, ← ent, pFin_infGL]; simp

theorem psiN_infGL (u : GL (Fin a) (Cinf E)) :
    GlobalTheory.JSW.psiN (infGL E a u) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) := by
  have hs : GlobalTheory.Whittaker.superDiag (infGL E a u) = sInf E (GlobalTheory.Whittaker.superDiag u) := by
    simp only [GlobalTheory.Whittaker.superDiag, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      intro e; subst e; simp at hj
    exact infGL_apply_of_ne u hij
  have h := GlobalTheory.ThetaPoisson.adelicChar_sInf_sum (E := E) (n := 1) (fun _ => GlobalTheory.Whittaker.superDiag u) (fun _ => 1)
  simp only [Fin.sum_univ_one, mul_one, Pi.one_apply] at h
  rw [GlobalTheory.JSW.psiN, hs, h]

theorem map_pInf_mem_unipB {u : GA E a} (hu : u ∈ GlobalTheory.JSW.NA E a) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a) := by
  refine (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [ent, hu.1 i j hji, map_zero]
  · rw [ent, hu.2 i, map_one]

theorem ad_eq_ite_iff (x : Ad E) (c : Prop) [Decidable c] :
    x = (if c then 1 else 0) ↔ pInf E x = (if c then 1 else 0) ∧ pFin E x = (if c then 1 else 0) := by
  refine ⟨fun h => ?_, fun h => ad_ext ?_ ?_⟩
  · subst h; split_ifs <;> simp
  · rw [h.1]; split_ifs <;> simp
  · rw [h.2]; split_ifs <;> simp

theorem mem_mirS_iff {m : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) {q : GA E (m + 1)}
    (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin (m + 1)) (Cinf E)) :
    q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m ↔
      (q ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ ∀ j, ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
      y ∈ GlobalTheory.JSW.mirSet (Cinf E) m := by
  have hsup : ∀ w : HeightOneSpectrum (𝓞 E),
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E (m + 1) y) = 1 :=
    fun w => map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
  have hI : GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y := by
    rw [map_mul, hq, one_mul, pInf_infGL]
  have hF : GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q := by
    rw [map_mul, pFin_infGL, mul_one]
  have hrow : ∀ j, ((q * infGL E (m + 1) y : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (if j = Fin.last m then 1 else 0) ↔
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = (if j = Fin.last m then 1 else 0) ∧
      ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E))
        (Fin.last m) j = (if j = Fin.last m then 1 else 0) := by
    intro j
    rw [ad_eq_ite_iff, ← ent, ← ent, hI, hF]
  have hS : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.supS E (m + 1) S ↔ q ∈ GlobalTheory.JSW.supS E (m + 1) S := by
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    rw [map_mul, hsup, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hS.1 h1, fun j => ((hrow j).1 (h2 j)).2⟩, fun j => ((hrow j).1 (h2 j)).1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨hS.2 h1, fun j => (hrow j).2 ⟨h3 j, h2 j⟩⟩

end GlobalTheory.JSW.KirArchTransfer

namespace GlobalTheory.JSW.KirArchTransfer

theorem kirillov_arch : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  intro E _ _ _ m S b W q hbe hbC hbs hWe hWc hWg hq hWq
  classical
  by_cases hne : ∃ y₀ : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y₀ ∈ GlobalTheory.JSW.mirS E S m
  · obtain ⟨y₀, hy₀⟩ := hne
    have hP := ((mem_mirS_iff S hq y₀).1 hy₀).1
    have hiff : ∀ y, q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m ↔ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m :=
      fun y => (mem_mirS_iff S hq y).trans ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
    have heq : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
        ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y,
          F (q * infGL E (m + 1) (u * y)) =
            (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * F (q * infGL E (m + 1) y) := by
      intro F hF u hu y
      rw [map_mul, ← mul_assoc, comm_infGL hq u, mul_assoc, hF _ (infGL_mem_NA hu), psiN_infGL]
    obtain ⟨C, hC, hCp⟩ := hbC
    obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ := GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic E m (fun y => b (q * infGL E (m + 1) y))
      (fun y => W (q * infGL E (m + 1) y)) (heq b hbe) ⟨chart b q, hbs, fun y => chart_val b q y⟩
      ⟨GeneralLinearGroup.map (pInf E) '' C, hC.image continuous_map_pInf_here, fun y hy hb0 => by
        obtain ⟨u, hu, hu'⟩ := hCp _ ((hiff y).2 hy) hb0
        refine ⟨GeneralLinearGroup.map (pInf E) u, map_pInf_mem_unipB hu, _, hu', ?_⟩
        rw [map_mul, map_inv, map_mul, hq, one_mul, pInf_infGL]⟩
      (heq W hWe) hWc hWg (by simpa using hWq)
    refine ⟨X, inferInstance, ν, inferInstance, k, γ, hk, fun y hy => ?_⟩
    rw [← hK y ((hiff y).1 hy)]
    simp only [GlobalTheory.JSW.kerInf]
    congr 1
    funext x
    rw [map_mul, mul_assoc]
  · exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => 1, GlobalTheory.JSW.isRapidInf_dirac 1,
      fun y hy => (hne ⟨y, hy⟩).elim⟩

end GlobalTheory.JSW.KirArchTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfIsFubiniStudyOfRatFnFamilyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → M.SemiPos D := by
  first | exact @GlobalTheory.HSNef.semiPos_of_isFS | exact GlobalTheory.HSNef.semiPos_of_isFS | (intros; apply GlobalTheory.HSNef.semiPos_of_isFS <;> assumption)
end

