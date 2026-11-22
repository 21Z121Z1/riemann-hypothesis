import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0859
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0857
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0860
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0858
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0861
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0862
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0863

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapCompositionStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_composition : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F''), ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | exact GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentityStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_identity : ∀ (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ l : BC F F, ∀ T b, l.α T b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.bc_self | exact GlobalTheory.CompanionTheory.PerfVB.bc_self | (intros; apply GlobalTheory.CompanionTheory.PerfVB.bc_self <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowthStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_polynomial_growth : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r → Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf → φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ) (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧ ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | exact GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_units_trivialize_modulo_ideal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)), ⨆ a, V a = ⊤ →
    ∀ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) →
      (∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | exact GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | (intros; apply GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormulaStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_degree_one_tower_formula : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F'') (l : BC F F''), (∀ T b, l.α T b = n.α T (m.α T b)) → ∀ x : S ⊗[R] C1 F, th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | exact GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | (intros; apply GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFiniteStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_maps_bijective_finite : ∀ (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.th_bijective | exact GlobalTheory.CompanionTheory.PerfVB.th_bijective | (intros; apply GlobalTheory.CompanionTheory.PerfVB.th_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRankStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_fibre_rank_stalk_rank : ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K] (g : ℕ), (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) → ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | exact GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | (intros; apply GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatementStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dependency_statement : DepSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.depSt | exact GlobalTheory.CompanionTheory.FewEq.depSt | (intros; apply GlobalTheory.CompanionTheory.FewEq.depSt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernelStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generalized_inverse_of_unit_kernel : ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span | exact GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyDimensionLowerBound
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.FirstCohomologyLowerBound

theorem dim_le (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (g n : ℕ) (hg : ringKrullDim R = g)
    (I : Ideal R) (hne : I ≠ ⊤) (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = I) : g ≤ n := by
  have hm : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
    rwa [← hI p hp.1.1 hp.1.2]
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I _ hm
  have h2 : Submodule.spanRank I ≤ n := by
    rw [← hf]
    refine (Submodule.spanRank_span_le_card (R := R) (Set.range f)).trans (Cardinal.mk_range_le.trans ?_)
    simp
  have h3 : (IsLocalRing.maximalIdeal R).height ≤ n := by
    refine h1.trans ?_
    simpa using Cardinal.toENat.monotone' h2
  have h4 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) = ((g : ℕ∞) : WithBot ℕ∞) :=
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hg
  rw [WithBot.coe_inj.1 h4] at h3
  exact_mod_cast h3

theorem exists_ample (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  haveI := hA.proper
  obtain ⟨M, hM⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA)
  exact ⟨M, hM.isLB, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hM.isLB).2 hM⟩

theorem evc_lam' {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem triv_lam_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) :
    Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP, evc_lam' hL, lam_one_left]

theorem one_mem_locus {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB)
    (Z : Over S) (i : Z ⟶ A) (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) (T : Over S) :
    ∃ z : T ⟶ Z, z ≫ i = 1 := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine (h.2 T 1).1 ?_
  rw [triv_ev_iff hP, evc_lam' hL, MonObj.comp_one, lam_one_right]

theorem snd_smooth_proper {S : Scheme.{0}} (A T : Over S) [Smooth A.hom] [IsProper A.hom] :
    Smooth (snd A T).left ∧ IsProper (snd A T).left := by
  have h : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  exact ⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance⟩

theorem lam_triv_left {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over S} (x : T ⟶ A) (h : Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x))) :
    Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP] at h ⊢
  have e := congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) h
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc, evc_lam' hL, lam_comm] at e
  rwa [evc_lam' hL]

theorem finite_sections (hK : PositivityTheory.ObstructionTrivialLocus.KFinite) (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (Z : Over (Sp k)) (i : Z ⟶ A)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) : Set.Finite {σ : Sp k ⟶ Z.left | σ ≫ Z.hom = 𝟙 _} := by
  haveI := hA.comm
  haveI : IsClosedImmersion i.left := h.1
  have hF := hK (Sp k) A hA L hL hamp k (𝟙 _)
  refine Set.Finite.of_finite_image (f := fun σ ↦ σ ≫ i.left) ((hF.image fun x ↦ x.left).subset ?_)
    (fun a _ b _ e ↦ (cancel_mono i.left).1 e)
  rintro _ ⟨σ, hσ, rfl⟩
  let z : Over.mk (𝟙 (Sp k)) ⟶ Z := Over.homMk σ hσ
  refine ⟨z ≫ i, lam_triv_left hL _ ((h.2 _ _).2 ⟨z, rfl⟩), rfl⟩

theorem stalk_local (X : Scheme.{0}) (x : X) : IsLocalRing (X.presheaf.stalk x) := inferInstance

theorem stalk_noeth (X : Scheme.{0}) [IsLocallyNoetherian X] (x : X) : IsNoetherianRing (X.presheaf.stalk x) :=
  inferInstance

theorem core (hFew : FewEqSt) (hFB : FlatBCSt) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] [Smooth A.hom]
    [IsProper A.hom] (hfin : Module.Finite k (HO1 A.hom)) (N : LB (A ⊗ A).left) (hN : N.IsLB) (Z : Over (Sp k))
    (i : Z ⟶ A) (hi : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (y₀ : Sp R ⟶ A.left) (g : ℕ) (hdim : ringKrullDim R = g) (I : Ideal R) (hne : I ≠ ⊤)
    (hrad : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (hJ : ∀ J : Ideal R, (∃ z : Sp (R ⧸ J) ⟶ Z.left, z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ y₀) ↔ I ≤ J) :
    g ≤ Module.finrank k (HO1 A.hom) := by
  let T : Over (Sp k) := Over.mk (y₀ ≫ A.hom)
  let y : T ⟶ A := Over.homMk y₀ rfl
  have hs := snd_smooth_proper A T
  obtain ⟨f, hf⟩ := hFew R (A ⊗ T).left (snd A T).left (Module.finrank k (HO1 A.hom))
    hs.1 hs.2 (fun X' s' φ h ↦ GlobalTheory.T.closed_fibre_structure_cohomology_finite hFB k A hfin R _ X' s' φ h)
    (ev N (fst A T) (snd A T ≫ y)) (pull_isLB hN _) I hne
    (fun J ↦ (GlobalTheory.T.trivial_locus_represents_triviality A A Z N hN i hi T y (spMap (Ideal.Quotient.mk J))).trans (hJ J))
  exact dim_le R g _ hdim I hne hrad f hf

theorem first_cohomology_dimension_lower_bound : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim := by
  intro hTL hKF hFB hFew hSD k _ _ A _ g hA hsm hfin
  obtain ⟨L, hL, hamp⟩ := exists_ample k A hA
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  haveI hnoeth : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨Z, i, hi⟩ := hTL (Sp k) A A hA hnoeth (abelian₂ A L) hP (triv_lam_one A L hL)
  haveI : IsClosedImmersion i.left := hi.1
  haveI : LocallyOfFiniteType Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hcl := GlobalTheory.T.finitely_many_sections_points_closed k Z.left Z.hom (finite_sections hKF k A hA L hL hamp Z i hi)
  let e : Sp k ⟶ A.left := (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left
  have he : e ≫ A.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp k)) ⟶ A)
  let p : Sp k := IsLocalRing.closedPoint k
  obtain ⟨z, hz⟩ := one_mem_locus A L hL Z i hi (Over.mk (𝟙 (Sp k)))
  have hx : e.base p ∈ Set.range i.left := ⟨z.left.base p, by
    have : z.left ≫ i.left = e := congrArg (fun q ↦ q.left) hz
    rw [← this]; rfl⟩
  have hd := hSD k A.left A.hom e g he hsm p
  generalize (e.base p : A.left) = x at hx hd
  obtain ⟨I, hne, hrad, hJ⟩ := GlobalTheory.T.stalk_ideal_represents_closed_subscheme A.left Z.left i.left x hx hcl
  exact @core hFew hFB k _ A _ _ _ hfin (abelian₂ A L) hP Z i hi (A.left.presheaf.stalk x) _ (stalk_local A.left x)
    (stalk_noeth A.left x) (A.left.fromSpecStalk x) g hd I hne hrad hJ

end GlobalTheory.CompanionTheory.FirstCohomologyLowerBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_rank_bound_at_closed_point : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | exact GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | (intros; apply GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_data_cohomology_base_change : ∀ (R A B C H S : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C] [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B) (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B), g ∘ₗ f = 0 → π ∘ₗ j = LinearMap.id → g ∘ₗ j = 0 → π ∘ₗ f = 0 → j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id → Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | exact GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | (intros; apply GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv <;> assumption)
end

