import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3420
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNon
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreH1

theorem resG_appLE {Y : Scheme.{0}} {K : Type} [CommRing K] (s : Y ⟶ Sp K) {V V' : Y.Opens} (h : V' ≤ V)
    (x : Γ(Sp K, ⊤)) : resG Y h ((s.appLE ⊤ V le_top).hom x) = (s.appLE ⊤ V' le_top).hom x := by
  exact congrArg (fun φ : Γ(Sp K, ⊤) ⟶ Γ(Y, V') => φ.hom x)
    (Scheme.Hom.appLE_map s (U := ⊤) le_top (homOfLE h).op)

theorem fieldDep : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (J : Type) (W : J → A.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → ∀ (e : Fin (g + 1) → ∀ i i' : J, Γ(A.left, W i ⊓ W i')), (∀ b i i' i'', resG A.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(A.left, W i), ∀ i i', ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG A.left inf_le_left (h i) - resG A.left inf_le_right (h i') := by
  intro K _ A _ g hA hsm J W hW hcov e he
  haveI := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set A.left))
    (fun i => (W i).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ i, W i) := by rw [hcov]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx)
  let σ : Fin t.card → J := fun k => (t.equivFin.symm k).1
  have hσ : ⨆ k, W (σ k) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨t.equivFin ⟨i, hi⟩, by simpa [σ] using hx⟩
  obtain ⟨hfin, hrk⟩ := GlobalTheory.T.abelian_cech_h1_trivial_bundle_rank_bound K A g hA hsm (Fin t.card) (fun k => W (σ k)) (fun k => hW _) hσ
  obtain ⟨c, hc, h', hh'⟩ := GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles K A.left A.hom g (Fin t.card) (fun k => W (σ k)) hfin hrk
    (fun b k k' => e b (σ k) (σ k')) (fun b k k' k'' => he b _ _ _)
  refine ⟨c, hc, ?_⟩
  exact GlobalTheory.T.cechCocycle_coboundary_of_coveringSubfamily A.left J W (Fin t.card) σ hσ
    (fun i i' => ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i') (by
      intro i i' i''
      simp only [map_sum, map_mul, resG_appLE]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, he b]) h' hh'

theorem fibre_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hprop hamp U n v hv huniq J W hWa hcov hWU m hm A _ ι hpb e he
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hA, hsm⟩ := GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame E H X t hprop U n v hv huniq m hm A ι hpb
  have hsq := hpb.1
  have hw : ι ≫ t.G.hom = A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U := hsq.w
  have htop : ⨆ i, ι ⁻¹ᵁ W i = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : t.G.hom.base (ι.base x) ∈ (U.1 : Set X) := by
      change (ι ≫ t.G.hom).base x ∈ _
      rw [hw, ← U.2.range_fromSpec]
      exact ⟨_, rfl⟩
    have hx' : ι.base x ∈ (⨆ i, W i) := by rw [hcov]; exact hx
    rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
    exact hx'
  have haff : ∀ i, IsAffineOpen (ι ⁻¹ᵁ W i) := fun i =>
    GlobalTheory.T.isAffineOpen_preimage_quotientFibre X t.G.left t.G.hom U m A.left A.hom ι hsq (W i) (hWa i) (hWU i)
  obtain ⟨c, hc, h, hh⟩ := fieldDep (Γ(X, U.1) ⧸ m) A n hA hsm J (fun i => ι ⁻¹ᵁ W i) haff htop e he
  choose r hr using fun b => Ideal.Quotient.mk_surjective (c b)
  refine ⟨r, ?_, h, fun i i' => ?_⟩
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hc
    refine ⟨b, fun hmem => hb ?_⟩
    rw [← hr b]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  · rw [← hh i i']
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst X t.G.left t.G.hom U m A.left A.hom ι hw (W i ⊓ W i') (inf_le_left.trans (hWU i))
      (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx), hr b]

end GlobalTheory.FibreH1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMul
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SurjD

theorem exists_fin_sum_tmul {R D M : Type*} [CommRing R] [CommRing D] [Algebra R D] [AddCommGroup M]
    [Module R M] (z : D ⊗[R] M) : ∃ (n : ℕ) (d : Fin n → D) (m : Fin n → M), z = ∑ i, d i ⊗ₜ m i := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  refine ⟨S.card, fun i ↦ (S.equivFin.symm i).1.1, fun i ↦ (S.equivFin.symm i).1.2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp S.equivFin.symm (fun p : S ↦ p.1.1 ⊗ₜ p.1.2)).symm

theorem cohom_of_cob {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {u a b c : Fn1 X} (h : Cohom W u a) (k : Fn0 X) (hk : IsCob W c k)
    (ha : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D), a D D' φ x = c D D' φ x + b D D' φ x) : Cohom W u b := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨fun D _ _ x ↦ k₀ D x + k D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have h1 := hk₀ D D' φ x hx
  have h2 := hk D D' φ x hx
  have h3 := ha D D' φ x
  simp only [Fn1.add, Fn1.neg] at h1 ⊢
  rw [map_add]
  linear_combination h1 + h2 + h3

end GlobalTheory.PtExt.SurjD

open GlobalTheory.PtExt.SurjD in

theorem GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  intro H R _ B _ g hB hg D _ _ u hu
  obtain ⟨B', _, π, q, hpb, hB', hg', hq, hfst, hsnd⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_spec_algebra_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (fst (SpAlg R D) B), ← Category.assoc, hfst]
    rfl
  have hu' := (GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole R D (algebraMap R D) _ B' q w u).1 hu
  have hsurj := GlobalTheory.PtExt.toH1O_surjective_of_abelian H D B' g hB' hg'
  obtain ⟨f', hf'⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective D B' hsurj (bcPull w u) hu'
  obtain ⟨hFree, -, hBC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  have hbc := (hBC R B g hB hg D B' π hpb).1
  have hall : prim (dp0 D) (𝟙 _) B' = ⊤ := (hFree D B' g hB' hg').1
  have hmem : H1.mk _ f' ∈ prim (dp0 D) (𝟙 _) B' := by rw [hall]; exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hbc.2 ⟨H1.mk _ f', hmem⟩
  obtain ⟨n, d, m, rfl⟩ := exists_fin_sum_tmul z
  choose β hβ using fun i ↦ H1.mk_surjective _ (m i).1
  refine ⟨n, d, β, ?_⟩
  let mB := (GlobalTheory.Published.AbelianDeRham.bcMor hpb).isMor
  let S : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _)) := ∑ i, d i • mB.coef.pullbackOneCocycle (β i)
  have hcl : H1.mk _ f' = H1.mk _ S := by
    have e := congrArg Subtype.val hz
    simp only [map_sum, liftSemi_tmul] at e
    rw [← e]
    simp only [S, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, GrpMor.coe_pull]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hβ i]
    rfl
  obtain ⟨g₀, hg₀⟩ := H1.mk_eq_mk.1 hcl
  obtain ⟨hadd, -, hcob⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  obtain ⟨k, hk⟩ := hcob g₀
  have hsplit : f' = ⟨d0 _ g₀, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g₀⟩ + S := Subtype.ext (by simp [hg₀])
  have hC : Cohom (whole B') (bcPull w u) (fv S) := by
    refine cohom_of_cob hf' k hk ?_
    rw [hsplit, hadd]
    intros
    rfl
  have hsum := GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq R D B B' q w π hfst hsnd mB (Fin n) d β
  obtain ⟨k', hk'⟩ : ∃ k, IsCob (whole B') (bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg)) k := by
    obtain ⟨k', hk'⟩ := hC
    refine ⟨k', ?_⟩
    have e : bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg) = (bcPull w u).add (fv S).neg := by
      rw [← hsum]; rfl
    rw [e]; exact hk'
  have hsm : IsCoc (whole _) (sumMul d fun i ↦ fv (β i)) :=
    (GlobalTheory.PtExt.SumMulFacts.main R D B (Fin n) d _).1 fun i ↦ (fv_isCoc_and_ev_eq R B (β i)).1
  have hdiff : IsCoc (whole _) (u.add (sumMul d fun i ↦ fv (β i)).neg) := by
    intro E _ _ E' _ _ E'' _ _ φ ψ x hx
    have h1 := hu E E' E'' φ ψ x hx
    have h2 := hsm E E' E'' φ ψ x hx
    simp only [Fn1.add, Fn1.neg, map_add, map_neg]
    linear_combination h1 - h2
  exact GlobalTheory.T.isPointwiseCoboundary_of_pullbackBaseChange_isIso R D (algebraMap R D) _ B' q w hq _ hdiff ⟨k', hk'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem scalar_pullback_spec_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (x y : A) :
    scal p (x * y) = scal p x * scal p y := by
  unfold scal; rw [map_mul, map_mul]

theorem Trait.exp_mul_left : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  intro R _ _ _ D C W _ _ _ T k s F a b c ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩
  refine ⟨DVR.SecOps.secScale (scal T.G.hom c) σ, ⟨σ', f', ?_, hP, hE⟩, ?_⟩
  · intro Z r z J J' hJ hJ'
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hC Z r z J J' hJ hJ', scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring
  · intro Z p p' hp z J hJ
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hs Z p p' hp z J hJ, scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspValueLePhiComplementStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_value_le_phi_complement : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  first | exact @GlobalTheory.HSApp.exists_cusp_value_le_phi | exact GlobalTheory.HSApp.exists_cusp_value_le_phi | (intros; apply GlobalTheory.HSApp.exists_cusp_value_le_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirEqZeroOfConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstPointCone

theorem unitOn_one {A : Type} [CommRing A] : unitOn (1 : Aˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem dir_eq_zero_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i, t i ∈ maximalIdeal R) → (∀ i y z, gam i y z = gam i z y) → ∀ (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r, (ρ r).snd = 0) → IsConstAlong Q t gam ρ a → a = 0 := by
  intro R _ _ _ Q m t gam hmon hli _ hs k _ _ ρ a hρ hc
  have hρc : constHom ρ = ρ := by
    ext r
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [constHom, TrivSqZeroExt.algebraMap_eq_inl, hρ]
  obtain ⟨B', _, π₁, π₂, w, c', h1, h2, h3, hw, hc', hrel⟩ := hc
  rw [hρc] at h2 hc' hrel
  have hπ : π₁ = π₂ := GlobalTheory.T.groupPullback_abelianScheme_dualNumber_eq k Q.P.A Q.P.g B' ρ π₁ π₂ Q.P.isAb Q.P.smoothDim h1 h2 h3
  subst hπ
  have hab : IsAbelianScheme B' :=
    (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback ρ Q.P.A B' π₁ Q.P.g h1 Q.P.isAb Q.P.smoothDim).1
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.pulledBackLineBundle_automorphism_eq_const B' Q.P.L π₁ hab Q.P.isLB w hw
  obtain ⟨zz⟩ : Nonempty (Sp (DualNumber k)) := inferInstance
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L zz J := by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB zz (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    exact ⟨J, hJ⟩
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₁), fun _ => J (c' x ≫ π₁))) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn lam) := by
    intro x
    have hmem : π₁ (c' x zz) ∈ Q.P.L.U (J (c' x ≫ π₁)) := by
      have := hJ (c' x ≫ π₁)
      simpa using this
    rw [hlam _ (c' x) zz _ hmem, (hc' x).1]
  have htne := GlobalTheory.T.monomialBoundaryFamily_param_ne_zero Q t gam hmon hli hs
  have key : ∀ y z, ∑ i, a i * (gam i y z : k) = 0 := by
    intro y z
    obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.exists_unitPartOfPeriodTau_monomial Q t gam hmon hs htne y z
    let e : (DualNumber k)ˣ := ⟨1 + TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)),
      1 - TrivSqZeroExt.inr (∑ i, a i * (gam i y z : k)), by ext <;> simp, by ext <;> simp⟩
    have h := hrel y z τ₀ hτ e rfl zz J hJ
    rw [hW (y + z), hW y, hW z, hW 0] at h
    have h' : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) = gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn 1) := by
      rw [unitOn_one, map_one]
      have hG : ∀ G : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ, G * G⁻¹ * G⁻¹ * G = 1 := fun G => by group
      rw [hG, _root_.one_mul] at h
      exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
    have he := GlobalTheory.T.dualNumber_unit_eq_of_germ_eq k zz _ _ h'
    have := congrArg (fun u : (DualNumber k)ˣ => TrivSqZeroExt.snd (u : DualNumber k)) he
    simpa [e] using this
  exact GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero gam k a hli key

end GlobalTheory.ConstPointCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DeepDiv

theorem yK_th_ne_zero {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V}
    {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem yK_th_eq {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V}
    {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam) :
    𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V)
      (RatModel.valLoc (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) z₁
        (by
          have : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
          rwa [Scheme.range_fromSpecStalk] at this)
        ⟨X₁.S.th a / X₁.S.th x₀, hd.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  set y' := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y := jK V ≫ y' with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
  have h1 : X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀) * X₁.M.val y (X₁.S.th x₀) := by
    conv_lhs => rw [e]
    exact RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [h1]
  congr 1
  exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' _ ⟨_, hd.2 a⟩

end GlobalTheory.Poinc.Sep.DeepDiv

open GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.DeepDiv.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ :=
  GlobalTheory.T.dividingLabel_persists_thetaSetupTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRham
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem sndPull_cohom_zero_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP v hv u hu
  have hFree : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hHDR).1
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have hgAB : SmoothOfRelativeDimension (g + g) (A ⊗ B).hom := AbDual.smooth_prod hgA hgB
  obtain ⟨u', hu', k1, c1⟩ := GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R (A ⊗ B) P.ι P.U hP.cover u hu
  obtain ⟨f, k2, c2⟩ := GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective R (A ⊗ B) (GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian hHDR R (A ⊗ B) (g + g) hAB hgAB) u' hu'
  have hprim : CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) := by
    have h : AllPrim (dp0 R) (𝟙 _) (A ⊗ B) := (hFree R (A ⊗ B) (g + g) hAB hgAB).1
    rw [primDR, h]; trivial
  obtain ⟨k3, c3⟩ := GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob R A B f hprim v
  refine ⟨fun D _ _ x ↦ (k1 (DualNumber D) (ptV v x)).snd + (k2 (DualNumber D) (ptV v x)).snd + k3 D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have e1 := congrArg TrivSqZeroExt.snd (c1 _ _ (epsHom φ) (ptV v x) (sm_ptV P hv hx))
  have e2 := congrArg TrivSqZeroExt.snd (c2 _ _ (epsHom φ) (ptV v x) (sm_whole _))
  have e3 := c3 D D' φ x (sm_whole _)
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
    TrivSqZeroExt.snd_sub, spOver_epsHom_ptV, snd_epsHom] at e1 e2 e3 ⊢
  rw [map_add, map_add]
  linear_combination e1 + e2 + e3

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartValueTranslateProdTangentsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eps_part_value_translate_prod_tangents : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g → ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)), (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) → ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O), (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := by
  first | exact @GlobalTheory.EpsAdd.snd_valR_mul_prod | exact GlobalTheory.EpsAdd.snd_valR_mul_prod | (intros; apply GlobalTheory.EpsAdd.snd_valR_mul_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyCloseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  first | (exact @GlobalTheory.HInvAic.main) | (exact GlobalTheory.HInvAic.main) | (intros; apply GlobalTheory.HInvAic.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonalStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chernRepresentative_contraction_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  first | exact @GlobalTheory.PtExt.exists_chernRep_contr_of_orth | exact GlobalTheory.PtExt.exists_chernRep_contr_of_orth | (intros; apply GlobalTheory.PtExt.exists_chernRep_contr_of_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalTrait_system_at_closedPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧ (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  first | exact @GlobalTheory.Poinc.PreSys.main | exact GlobalTheory.Poinc.PreSys.main | (intros; apply GlobalTheory.Poinc.PreSys.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  first | exact @GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | exact GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | (intros; apply GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed <;> assumption)
end

