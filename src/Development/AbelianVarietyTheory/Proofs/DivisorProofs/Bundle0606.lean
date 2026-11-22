import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEq
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
section
namespace GlobalTheory.LFun

theorem norm_le_card_of_heckeVec_eq_smul :
    ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) →
      (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) →
      {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x →
      ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  intro G _ K V _ _ ρ Bf hsym hpos hinv h x c hh hfin hx hc
  classical
  have hnn : ∀ y, 0 ≤ (Bf y y).re := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by rw [hsym x y]; simp
      re_inner_nonneg := hnn
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have cs : ∀ y, ‖Bf x y‖ * ‖Bf y x‖ ≤ (Bf x x).re * (Bf y y).re :=
    fun y => @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ core x y
  have hr : 0 < (Bf x x).re := hpos x hx
  have hb : ∀ g, ‖Bf x (ρ g x)‖ ≤ (Bf x x).re := by
    intro g
    have h1 := cs (ρ g x)
    rw [hinv, hsym x (ρ g x), RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (Bf x (ρ g x))]
  have hxx : ‖Bf x x‖ = (Bf x x).re := by
    have e : (starRingEnd ℂ) (Bf x x) = Bf x x := (hsym x x).symm
    rw [RCLike.conj_eq_iff_re] at e
    rw [← e]
    simp [abs_of_pos hr]
  set S := hfin.toFinset
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ S := by
    intro q hq
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ S, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  have key : c * Bf x x = ∑ q ∈ S, h q.out * Bf x (ρ q.out x) := by
    rw [← smul_eq_mul, ← map_smul, ← hc, hsum, map_sum]
    simp
  have hcard : Nat.card {q : G ⧸ K // h q.out ≠ 0} = S.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hle : ‖c‖ * (Bf x x).re ≤ (S.card : ℝ) * (Bf x x).re := by
    calc ‖c‖ * (Bf x x).re = ‖c * Bf x x‖ := by rw [norm_mul, hxx]
      _ = ‖∑ q ∈ S, h q.out * Bf x (ρ q.out x)‖ := by rw [key]
      _ ≤ ∑ q ∈ S, ‖h q.out * Bf x (ρ q.out x)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, (Bf x x).re := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        calc ‖h q.out‖ * ‖Bf x (ρ q.out x)‖ ≤ 1 * (Bf x x).re :=
              mul_le_mul (hh _) (hb _) (norm_nonneg _) zero_le_one
          _ = (Bf x x).re := one_mul _
      _ = (S.card : ℝ) * (Bf x x).re := by simp
  rw [hcard]
  exact le_of_mul_le_mul_right hle hr

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantOrdersProperty
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_detElt_orders_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → Δ ∣ Δ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hD hD' hO hO'
  obtain ⟨hAdom, -, hker, -, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨hmu0, hmu, -⟩ := GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hinA : ∀ x : Ainf p O, (inA x : RL p O Λ) = x ⊗ₜ[ℤ_[p]] (1 : Λ) := fun x => by
    first | rfl | simp [inA, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self]
  have hθ : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x, f (inA x) = WittVector.fontaineTheta O p x := by
    intro σ f hf x; rw [hinA, hf, map_one, mul_one]
  have hθxi : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hψmu : ψ (inA (mu ε)) = inA (nu ε) := by
    rw [hinA, hψ, hinA, phiInv_mu]

  have hu' : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → algebraMap O C (f (ψ Δ')) ≠ 0 := by
    intro σ f hf h0
    obtain ⟨k, hk⟩ := hD'.1
    have h1 := congrArg (fun x => algebraMap O C (f (ψ x))) hk
    simp only [map_pow, map_mul, hψmu, hθ σ f hf, h0, zero_mul] at h1
    exact pow_ne_zero N ((map_ne_zero_iff _ hinj).mpr hnu) h1
  obtain ⟨g, hΔg, g₁, hgg⟩ := hD.2
  obtain ⟨g', hΔg', -⟩ := hD'.2
  let ι := {q : (Λ →+* O) × (RL p O Λ →+* O) // IsTheta q.1 q.2}
  have hξ : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ (xi ε) hxi
  obtain ⟨b, hb⟩ := GlobalTheory.DetInv.dvd_of_lead_orders_eq (RL p O Λ) C ι
    (fun i => (algebraMap O C).comp i.1.2) (inA (xi ε)) N (fun i => a i.1.1)
    (fun i => c i.1.1) (fun i => c' i.1.1) Δ Δ' (ψ Δ) (ψ Δ') g g' g₁ hξ
    (fun i => by
      show algebraMap O C (i.1.2 (inA (xi ε))) = 0
      rw [hθ _ _ i.2, hθxi, map_zero])
    (fun r hr => GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ r (fun σ f hf => hinj (by
      simpa using hr ⟨(σ, f), hf⟩)))
    (fun i => (hO i.1.1 i.1.2 i.2).1) (fun i => (hO i.1.1 i.1.2 i.2).2.1)
    (fun i => (hO i.1.1 i.1.2 i.2).2.2) (fun i => (hO' i.1.1 i.1.2 i.2).2.2)
    hΔg hΔg' (fun i => by simpa using hu' i.1.1 i.1.2 i.2) hgg.symm
  haveI := hAdom
  obtain ⟨Δs, hΔs⟩ := hD.1
  have hcoeff : (mu ε ^ N).coeff 0 ≠ 0 := by
    haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
    have : ∀ n : ℕ, (mu ε ^ n).coeff 0 = (mu ε).coeff 0 ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, WittVector.mul_coeff_zero, ih, pow_succ]
    rw [this]; exact pow_ne_zero N hmu0
  refine GlobalTheory.DetInv.dvd_of_twisted_eq (RL p O Λ) ψ (inA (mu ε ^ N)) Δ Δs Δ' g b
    (GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ _ (pow_ne_zero N hmu))
    (by
      show Δ * Δs = algebraMap (Ainf p O) (RL p O Λ) (mu ε ^ N)
      rw [map_pow]; exact hΔs.symm) hΔg (by rw [hb] at hΔg'; exact hΔg') ?_
  exact GlobalTheory.T.ainf_coefficient_psi_property p C v O hv Λ ψ hψ (mu ε ^ N) hcoeff

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSurjectiveNilpotentKerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  first | exact @GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | exact GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | (intros; apply GlobalTheory.FerrandPush.res_surjective_nilpotent_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback : ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X) (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  first | exact @GlobalTheory.sectionComponents_preimage_of_isPullback | exact GlobalTheory.sectionComponents_preimage_of_isPullback | (intros; apply GlobalTheory.sectionComponents_preimage_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_isUnit_zero (U : Scheme) (h : IsUnit (0 : Γ(U, ⊤))) : IsEmpty U := by
  constructor
  intro x
  have h01 : (0 : Γ(U, ⊤)) = 1 := isUnit_zero_iff.1 h
  have := congrArg (U.presheaf.germ ⊤ x trivial).hom h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_prim_zero (U : Scheme)
    (ζ : _root_.GlobalTheory.EtC.Prim 0 Γ(U, ⊤)) : IsEmpty U :=
  isEmpty_of_isUnit_zero U (by simpa using ζ.2.1)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma sec_eq_of_isEmpty' {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R) (U : Scheme)
    [IsEmpty U] (a b : _root_.GlobalTheory.EtC.Sec F U) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F U).1 a b
    ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.twPair_spec (q : ℕ) (i j : ℤ) :
    _root_.GlobalTheory.EtC.IsTwPair (_root_.GlobalTheory.EtC.twPair q i j) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsTwPair
    intro U ζ
    haveI := isEmpty_of_prim_zero U ζ
    exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact (_root_.GlobalTheory.EtC.TwPairUniq.main q i j).1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.kumT_spec (q : ℕ) : _root_.GlobalTheory.EtC.IsKum q (_root_.GlobalTheory.EtC.kumT q) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsKum
    refine ⟨fun V U g v h => ?_, fun U ζ v w _ => ?_⟩
    · haveI := isEmpty_of_isUnit_zero U (by simpa using h)
      haveI : IsEmpty V := ⟨fun x => IsEmpty.false (g.base x)⟩
      exact sec_eq_of_isEmpty' _ _ _ _
    · haveI := isEmpty_of_prim_zero U ζ
      exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact _root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.restrMap_spec {S R : Type} [CommRing S] [CommRing R] (φ : R →+* S)
    (F : _root_.GlobalTheory.EtC.Shv S) (U : Scheme.{0}) (a : _root_.GlobalTheory.EtC.Sec F U) :
    (_root_.GlobalTheory.EtC.restrMap φ F).app U 0
        (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι S F) a) =
      _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R ((_root_.GlobalTheory.EtC.restr φ).obj F))
        (show _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.restr φ).obj F) U from a) :=
  _root_.GlobalTheory.EtC.restrMap_spec' R S φ F U a

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEqStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ), ρ + k + 2 ≤ r → nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  first | exact @GlobalTheory.FinGL.RootExchange.nPos_succ | exact GlobalTheory.FinGL.RootExchange.nPos_succ | (intros; apply GlobalTheory.FinGL.RootExchange.nPos_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCup
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedCup

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem cpush_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (a : CohomologyClass K I n) : cpush K (𝟙 I) n a = a := by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

def semiPre {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K') :
    SemiMap T K' where
  app U s := (ρ.app U s).comp ((u.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    change Sec.res g (ρ.app _ s (Sec.map (u.f s) a)) = ρ.app _ s (Sec.map (u.f s) (Sec.res g a))
    rw [ρ.nat, sec_map_res]
  comm U s t a := by
    change Sec.map (_ : _ ⟶ _) (ρ.app U s (Sec.map (u.f s) a)) = ρ.app U t (Sec.map (u.f t) (Sec.map (T.d s t) a))
    rw [ρ.comm, ← sec_map_comp, ← sec_map_comp, u.comm]

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (u : I ⟶ K)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x = Sec.map (u.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem semiPre_op {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K')
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) T n) :
    (semiPre u ρ).op.app E n x = ρ.op.app E n (cpush _ u n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n (zcomp α (Cocycle.ofHom u) (add_zero n))
  change _ = ρ.op.app E n (CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)))
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n _ β hβ]
  refine (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R (semiPre u ρ)).2 E n α β (fun p s h U y => ?_)
  rw [hβ p s h U y]
  change ρ.app U s (ev (α.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y) = _
  rw [ev_comp_ofHom]
  rfl

theorem semiMap_cup : ∀ (S R : Type) [CommRing S] [CommRing R] {I J T : Cx S} {I' J' K' : Cx R} (τ : Pair I J T) (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (σ : SemiMap T K'), (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b)) → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains S).obj E) I n) (b : CohomologyClass ((chains S).obj E) J m), σ.op.app E k (τ.cup E hk a b) = ν.cup E hk (ρ₁.op.app E n a) (ρ₂.op.app E m b) := by
  intro S R _ _ I J T I' J' K' τ ν ρ₁ ρ₂ σ hσ E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW S τ hk).1 α β
  obtain ⟨α', hα'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).1 E m β
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).1 E k γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW S τ hk).2 α β γ hγ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).2 E k γ γ' hγ',
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).2 E n α α' hα', (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).2 E m β β' hβ']
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 α' β' γ' ?_).symm
  intro N w h U x
  rw [hγ' N w h U x, hγ N w h U x, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, hσ, ← hα', ← hβ', Units.smul_def]

theorem reduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j),
    red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  intro Q q _ hqQ E n m i j a b
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp hqQ)⟩
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod Q) (res _ (tw Q i)) (res _ (tw Q j))
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod Q) τ hτ).1 (twPair Q i j) (𝟙 _) (𝟙 _)
  have hcup : cup Q a b = cpush _ u _ (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod Q) τ (twPair Q i j) (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
    rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_semiMap_of_tensorPairing Q (ZMod q) τ hτ (twPair q i j) (redMap Q q i) (redMap Q q j)
  have h1 := semiMap_cup (ZMod Q) (ZMod q) τ (twPair q i j) (redMap Q q i) (redMap Q q j) σ hσ E rfl a b
  rw [hcup]
  change (redMap Q q (i + j)).op.app E (n + m) (cpush _ u _ _) = (twPair q i j).cup E rfl _ _
  rw [← semiPre_op]
  change _ = (twPair q i j).cup E rfl ((redMap Q q i).op.app E n a) ((redMap Q q j).op.app E m b)
  rw [← h1]
  have hres := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q i
  have hresj := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q j
  have htw := GlobalTheory.T.isTateTwistResolution_tensor_flat Q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) hres.1 hresj.1 hresj.2.1 τ hτ
  have hflat := GlobalTheory.T.flat_tensor_of_flat_complexes (ZMod Q) τ hτ hres.2.1 hresj.2.1
  refine GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution Q q hqQ (i + j) _ htw hflat _ _ ?_ E (n + m) _
  intro U ζ
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [hσ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ ξ hξ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ j U ζ ξ hξ, (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 U ξ]
  change (redMap Q q (i + j)).app U 0 (Sec.map (u.f 0) _) = _
  rw [hu]
  change (redMap Q q (i + j)).app U 0 ((twPair Q i j).mul U 0 0 0 _ (resGen i ζ) (resGen j ζ)) = _
  rw [(GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique Q i j).1 U ζ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ (i + j) U ζ ξ hξ]

end GlobalTheory.EtC.RedCup

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDenseStatement
section
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_family_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ), (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ, MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | exact GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | (intros; apply GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense <;> assumption)
end

