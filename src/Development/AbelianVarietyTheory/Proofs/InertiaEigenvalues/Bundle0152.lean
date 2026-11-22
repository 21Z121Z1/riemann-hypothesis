import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
section
open ReciprocityTheory.Gal

open Polynomial IntermediateField

namespace GlobalTheory.ShapeNeg

theorem natDegree_minpoly_le_mul {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) (hx : IsIntegral K x) :
    (minpoly ℚ_[p] x).natDegree ≤ (minpoly K x).natDegree * Module.finrank ℚ_[p] K := by
  set E := K⟮x⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hx
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  have h1 : Module.finrank ℚ_[p] K * Module.finrank K E = Module.finrank ℚ_[p] E :=
    Module.finrank_mul_finrank ℚ_[p] K E
  rw [adjoin.finrank hx] at h1
  have hxE : x ∈ E := mem_adjoin_simple_self K x
  haveI : IsScalarTower ℚ_[p] E (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h2 : minpoly ℚ_[p] (⟨x, hxE⟩ : E) = minpoly ℚ_[p] x :=
    (minpoly.algebraMap_eq (algebraMap E (PadicAlgCl p)).injective (⟨x, hxE⟩ : E)).symm
  have h3 := minpoly.natDegree_le (A := ℚ_[p]) (⟨x, hxE⟩ : E)
  rw [h2] at h3
  rw [mul_comm]
  omega

theorem natDegree_minpoly_le_card_pow_eq_one {p : ℕ} [Fact p.Prime]
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {N : ℕ} [NeZero N] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ) :
    (minpoly K ζ).natDegree ≤ Nat.card {x : ZMod N // x ^ k = 1} := by
  classical
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hirr : Irreducible (minpoly K ζ) := minpoly.irreducible hint
  have hsep : (minpoly K ζ).Separable := hirr.separable
  have hspl : Splits ((minpoly K ζ).map (algebraMap K (PadicAlgCl p))) := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl, ← Nat.card_eq_fintype_card]
  have hχ : ∀ σ : Formalism.GaloisCohomology.GK p K, ((hζ.autToPow K σ : ZMod N)) ^ k = 1 := by
    intro σ
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 := hζ.autToPow_spec K (σ ^ k)
    rw [hfix σ] at h1
    have h0 : ζ ^ (1 % N) = ζ := by rw [hζ.eq_orderOf, pow_mod_orderOf, pow_one]
    have h2 : ζ ^ (hζ.autToPow K (σ ^ k) : ZMod N).val = ζ ^ (1 % N) := h1.trans h0.symm
    have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
    rw [← ZMod.val_one_eq_one_mod] at h3
    exact ZMod.val_injective N h3
  have horb : ∀ y : (minpoly K ζ).rootSet (PadicAlgCl p), ∃ σ : Formalism.GaloisCohomology.GK p K, σ ζ = y := by
    intro y
    have hy : aeval (y : PadicAlgCl p) (minpoly K ζ) = 0 :=
      (mem_rootSet.1 y.2).2
    have he : minpoly K ζ = minpoly K (y : PadicAlgCl p) :=
      minpoly.eq_of_irreducible_of_monic hirr hy (minpoly.monic hint)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (PadicAlgCl p)).1 he.symm
    exact ⟨σ, hσ⟩
  choose σ hσ using horb
  refine Nat.card_le_card_of_injective (fun y => ⟨(hζ.autToPow K (σ y) : ZMod N), hχ (σ y)⟩) ?_
  intro y y' hyy
  have h : (hζ.autToPow K (σ y) : ZMod N) = (hζ.autToPow K (σ y') : ZMod N) :=
    congrArg Subtype.val hyy
  have h' : (σ y) ζ = (σ y') ζ := by
    rw [← hζ.autToPow_spec K (σ y), ← hζ.autToPow_spec K (σ y'), h]
  exact Subtype.ext (by rw [← hσ y, ← hσ y']; exact h')

theorem exists_pow_ne_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  intro p _ K hK k hk
  by_contra hcon
  push_neg at hcon
  have hp : p.Prime := Fact.out
  set d := Module.finrank ℚ_[p] K with hd
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * d < p ^ n := ⟨2 * k * d, Nat.lt_pow_self hp.one_lt⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  have hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ := fun σ => hcon σ (n + 1) ζ hζ.pow_eq_one
  have hB := natDegree_minpoly_le_card_pow_eq_one hζ k hfix
  have hC : Nat.card {x : ZMod (p ^ (n + 1)) // x ^ k = 1} ≤ 2 * k := by
    by_cases h2 : p = 2
    · subst h2
      exact GlobalTheory.card_pow_eq_one_two_pow_le (n + 1) (by omega) hk
    · haveI : IsCyclic (ZMod (p ^ (n + 1)))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 (n + 1)
      have := GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (p ^ (n + 1)) hk
      omega
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  have hA := natDegree_minpoly_le_mul hK ζ hint
  have hcyc : cyclotomic (p ^ (n + 1)) ℚ_[p] = minpoly ℚ_[p] ζ := by
    refine minpoly.eq_of_irreducible_of_monic (GlobalTheory.Cyc.Model.cyc_irred n) ?_ (cyclotomic.monic _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos _)
  rw [← hcyc, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hA
  rw [← hd] at hA
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h1 : p ^ n ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ hp1
  have h2 : (minpoly K ζ).natDegree * d ≤ 2 * k * d := Nat.mul_le_mul_right _ (hB.trans hC)
  omega

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumberFieldAdjoinEq
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicNumberFieldGen

open Polynomial IntermediateField

theorem exists_rat_root_mem_adjoin (l : ℕ) [Fact l.Prime] (α : PadicAlgCl l) :
    ∃ β : PadicAlgCl l, ∃ g : ℚ[X], g.Monic ∧ g.natDegree = (minpoly ℚ_[l] α).natDegree ∧
      aeval β g = 0 ∧ α ∈ ℚ_[l]⟮β⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have fmon : (minpoly ℚ_[l] α).Monic := minpoly.monic (hint α)
  have fa0 : (minpoly ℚ_[l] α).aeval α = 0 := minpoly.aeval _ _
  have hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  have hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) := by
    simp only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
    exact fun x' h => h.2
  obtain ⟨δ, δpos, hball⟩ := Metric.isOpen_iff.1 hop α hmem
  have hn : (minpoly ℚ_[l] α).natDegree ≠ 0 := (minpoly.natDegree_pos (hint α)).ne'
  have hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree /
      ((minpoly ℚ_[l] α).natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) fmon hε
  obtain ⟨β, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖α - β‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have hβU := hball (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)
  have hgβ : aeval β g = 0 := by
    rw [Polynomial.mem_aroots] at hb
    simpa [Polynomial.aeval_map_algebraMap] using hb.2
  refine ⟨β, g, gmon, gdeg.symm, hgβ, ?_⟩
  refine IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _)
    (hint β) fun x' h1 h2 => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hβU
  exact hβU x' ⟨h1, h2⟩

end GlobalTheory.PadicNumberFieldGen

namespace GlobalTheory.PadicNumberFieldGen

open Polynomial IntermediateField

theorem exists_numberField_adjoin_eq : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∃ (F : Type) (_ : Field F) (_ : NumberField F) (c : F →+* PadicAlgCl l), IntermediateField.adjoin ℚ_[l] (Set.range c) = K := by
  intro l _ K hK
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] K
  have hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  obtain ⟨β, g, gmon, gdeg, hgβ, hαβ⟩ := exists_rat_root_mem_adjoin l (α : PadicAlgCl l)
  have hβQ : IsIntegral ℚ β := ⟨g, gmon, hgβ⟩
  haveI : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβQ
  haveI : NumberField ℚ⟮β⟯ := ⟨⟩
  refine ⟨ℚ⟮β⟯, inferInstance, inferInstance, (ℚ⟮β⟯).val.toRingHom, ?_⟩
  have hrange : Set.range (ℚ⟮β⟯).val.toRingHom = (ℚ⟮β⟯ : Set (PadicAlgCl l)) := by
    ext x; simp
  rw [hrange]
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have h1 : IntermediateField.adjoin ℚ_[l] (ℚ⟮β⟯ : Set (PadicAlgCl l)) = ℚ_[l]⟮β⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hle : ℚ⟮β⟯ ≤ (ℚ_[l]⟮β⟯).restrictScalars ℚ := by
        rw [IntermediateField.adjoin_simple_le_iff]
        exact IntermediateField.mem_adjoin_simple_self ℚ_[l] β
      exact hle hx
    · apply IntermediateField.adjoin.mono
      rw [Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ β
  rw [h1, hKα]
  symm
  haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_
  rw [IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]
  have hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0 := (gmon.map _).ne_zero
  have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) :=
    minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)
  calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hg0
    _ = g.natDegree := g.natDegree_map _

end GlobalTheory.PadicNumberFieldGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenCompactAnnihilatorScaledIntegersK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualScaledIntegers

theorem exists_open_compact_annihilator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  intro F E _ _ _ _ U A ψ hψ c hc
  have := U.ultraF
  have := U.lcF
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hop, hcp, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let D : AddSubgroup A.K :=
    { carrier := {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      zero_mem' := by
        intro z _
        simp [Et.psiK]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := ha z hz
        have h2 := hb z hz
        simp only [Et.psiK] at h1 h2 ⊢
        rw [mul_add, map_add, AddChar.map_add_eq_mul, h1, h2, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := ha z hz
        simp only [Et.psiK] at h1 ⊢
        rw [mul_neg, map_neg, AddChar.map_neg_eq_inv, h1, inv_one] }
  have hcs : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hM : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        rwa [smul_inv_smul₀ hc]
    rw [this]
    exact hcp.image (continuous_const_smul _)
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hDo : IsOpen (D : Set A.K) := by
    refine AddSubgroup.isOpen_of_mem_nhds D (g := 0) ?_
    have h := hM.eventually_forall_of_forall_eventually (x₀ := (0 : A.K))
      (P := fun b z => A.psiK ψ (z * b) = 1) (fun y _ => by
        have hc2 : Continuous fun p : A.K × A.K => Algebra.trace F A.K (p.2 * p.1) :=
          htr.comp (continuous_snd.mul continuous_fst)
        have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (((0 : A.K), y).2 * ((0 : A.K), y).1)) := by
          simpa using Metric.closedBall_mem_nhds (0 : F) one_pos
        filter_upwards [hc2.continuousAt.preimage_mem_nhds h0] with p hp
        exact hψ.1 _ (by simpa using hp))
    exact h
  refine ⟨D, rfl, hDo, ?_⟩
  have hU : {z : A.K | c • z ∈ A.OK} ∈ 𝓝 (0 : A.K) := by
    refine (hop.preimage hcs).mem_nhds ?_
    show c • (0 : A.K) ∈ A.OK
    rw [smul_zero, ← hR]
    exact R.zero_mem
  obtain ⟨M, N, hMU, -, -, -, hN, hMN, -⟩ :=
    (exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 _ hU
  refine hN.of_isClosed_subset (D.isClosed_of_isOpen hDo) fun b hb => ?_
  exact (hMN b).2 fun x hx => hb x (hMU hx)

end GlobalTheory.JR.DualScaledIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])

theorem selfDual_kx_exists : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveOfIsCplAt
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by
  algebraize [φ]
  have h1 : (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  let e : TensorProduct R (R ⧸ I) S ≃+* S ⧸ I.map φ :=
    (Algebra.TensorProduct.comm R (R ⧸ I) S).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv
  have h2 : (e : TensorProduct R (R ⧸ I) S →+* S ⧸ I.map φ).Flat := RingHom.Flat.of_bijective e.bijective
  have h3 := h1.comp h2
  convert h3 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have : (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S) = (1 : R ⧸ I) ⊗ₜ[R] (φ r) := by
    have := TensorProduct.smul_tmul (R := R) r (1 : R ⧸ I) (1 : S)
    simp only [Algebra.smul_def, mul_one] at this
    exact this
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_coe]
  rw [this]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
  simp [e]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I (φ r)

theorem exists_surjective_of_isCplAt : ∀ (R R' S S' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (π : R →+* R') (q' : Ideal R') [q'.IsPrime] (φ : R →+* S) (φ' : R' →+* S'), Function.Surjective π → IsCplAt (q'.comap π) φ → IsCplAt q' φ' → ∃ θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = φ'.comp π ∧ Function.Surjective θ ∧ RingHom.ker θ = (RingHom.ker π).map φ := by
  intro R R' S S' _ _ _ _ _ _ _ π q' _ φ φ' hπ h h'
  set J : Ideal S := (RingHom.ker π).map φ with hJ
  have hJm : J ≤ maximalIdeal S := by
    rw [h.max_eq]
    exact Ideal.map_mono (Ideal.ker_le_comap π)
  have hJt : J ≠ ⊤ := fun ht => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (ht ▸ hJm))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
  haveI : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI := h.noeth
  haveI := h.complete
  let ε : R' ≃+* R ⧸ RingHom.ker π := (RingHom.quotientKerEquivOfSurjective hπ).symm
  let ψ : R' →+* S ⧸ J :=
    (Ideal.quotientMap J φ Ideal.le_comap_map).comp (ε : R' →+* R ⧸ RingHom.ker π)
  have hψ : ∀ r, ψ (π r) = Ideal.Quotient.mk J (φ r) := by
    intro r
    have : ε (π r) = Ideal.Quotient.mk _ r := by
      apply ε.symm.injective
      simp [ε]
    simp [ψ, this]
  have hψ' : ψ.comp π = (Ideal.Quotient.mk J).comp φ := RingHom.ext hψ
  have hm : maximalIdeal (S ⧸ J) = (maximalIdeal S).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hmc : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S := by
    rw [hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hJm]
  have hc : IsCplAt q' ψ :=
    { noeth := inferInstance
      complete := by
        have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal S) (S ⧸ J)
        rwa [show algebraMap S (S ⧸ J) = Ideal.Quotient.mk J from rfl, ← hm] at this
      flat := (RingHom.Flat.of_bijective ε.bijective).comp (flat_quotientMap_map φ h.flat _)
      max_eq := by
        rw [hm, h.max_eq, Ideal.map_map, ← hψ', ← Ideal.map_map, Ideal.map_comap_of_surjective π hπ]
      comap_eq := by
        ext x
        obtain ⟨r, rfl⟩ := hπ x
        rw [Ideal.mem_comap, hψ, ← Ideal.mem_comap, hmc, ← Ideal.mem_comap, h.comap_eq, Ideal.mem_comap]
      res := by
        intro s
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨a, b, hb, hab⟩ := h.res s
        refine ⟨π a, π b, hb, ?_⟩
        rw [hψ, hψ, ← map_mul, ← map_sub, ← Ideal.mem_comap, hmc]
        exact hab }
  obtain ⟨e, he⟩ := GlobalTheory.T.completion_unique_up_to_iso R' (S ⧸ J) S' q' ψ φ' hc h'
  have hs : Function.Surjective ((e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J)) :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨(e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J), IsLocalHom.of_surjective _ hs, ?_, hs, ?_⟩
  · rw [RingHom.comp_assoc, ← hψ', ← RingHom.comp_assoc, he]
  · ext s
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.Pat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.FinPlaceApproxPos

theorem exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.FinPlaceApprox.approx_target F T t M
  set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  set d : ℕ := Ideal.absNorm J with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hdJ : ((d : ℤ) : 𝓞 F) ∈ J := by
    simpa [hd] using Ideal.absNorm_mem J
  have hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M := fun v hv =>
    Ideal.prod_le_inf.trans (Finset.inf_le hv)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  refine ⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩
  · have hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M := by
      apply hJv v hv
      have : ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F) := by push_cast; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hdJ
    have hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ)) := by
      have : ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F) := by simp
      rw [this, HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
    have : a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)
  · have h1 : φ a₀ ≥ -B := by
      have := hB ⟨φ, rfl⟩
      have := neg_abs_le (φ a₀)
      simp only at *
      linarith
    have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    have hNB : B < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil B) (by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [map_add, map_natCast]
    push_cast
    nlinarith

theorem approxpos_target : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M

end GlobalTheory.FinPlaceApproxPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
section
open Formalism.GaloisCohomology ReciprocityTheory.Gal

namespace GlobalTheory

theorem finite_H1_H2_of_localTateDuality : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hC, -, h11, h11f, h20⟩ := hT l K hK r M rho hr hrho
  obtain ⟨e⟩ := hC
  haveI hCfin : Finite (H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hAB := GlobalTheory.T.finite_of_bijective_pairing_zmod (l ^ r) _ _ _ _ ⟨e⟩ h11 h11f
  refine ⟨hAB.2, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K)))) :=
    Subtype.finite
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  exact Finite.of_injective _ h20.1

end GlobalTheory
end

