import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0858
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0864
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0865
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0857
import Development.WeilBound.CoreStatements.PadicHodgeComparison.UniqueSaturation.DescentOffPrescribedPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := GlobalTheory.T.trivial_pullback_gives_unit_cocycle
  have mingens := GlobalTheory.T.minimal_generators_local_ideal
  have flat := GlobalTheory.T.minimal_generators_base_change
  have dep := GlobalTheory.T.dependency_statement
  have fibre := GlobalTheory.T.first_cohomology_rank_bound_at_closed_point
  have cocycle := GlobalTheory.T.unit_cocycle_lift_modulo_maximal
  have finish := GlobalTheory.T.unit_cocycle_lift_minimal_generators
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.GenInv

variable {A : Type} [CommRing A] {M M' : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M']

noncomputable def proj (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) : M →ₗ[A] LinearMap.ker σ :=
  LinearMap.codRestrict _ (LinearMap.id - σ.smulRight v) (fun x => by
    simp [LinearMap.mem_ker, h])

theorem proj_coe (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : M) :
    (proj σ v h x : M) = x - σ x • v := rfl

theorem proj_ker (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : LinearMap.ker σ) :
    proj σ v h x = x :=
  Subtype.ext (by simp [proj_coe, LinearMap.mem_ker.1 x.2])

theorem apply_mem_smul_top (f : M →ₗ[A] M') (I : Ideal A) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : f x ∈ I • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem ker_finite [Module.Finite A M] (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    Module.Finite A (LinearMap.ker σ) :=
  Module.Finite.of_surjective (proj σ v h) (fun x => ⟨x, proj_ker σ v h x⟩)

theorem ker_free [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.Free A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI : Module.Projective A (LinearMap.ker σ) :=
    Module.Projective.of_split (LinearMap.ker σ).subtype (proj σ v h)
      (LinearMap.ext fun x => proj_ker σ v h x)
  haveI : Module.FinitePresentation A (LinearMap.ker σ) :=
    Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

noncomputable def kerEquiv (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    M ≃ₗ[A] A × LinearMap.ker σ :=
  LinearEquiv.ofLinear (σ.prod (proj σ v h))
    (LinearMap.coprod (LinearMap.toSpanSingleton A M v) (LinearMap.ker σ).subtype)
    (by
      ext x
      · simp [h]
      · simp [proj_coe, h]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [proj_coe, LinearMap.mem_ker.1 x.2])
    (by
      ext x
      simp [proj_coe])

theorem finrank_ker [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.finrank A M = 1 + Module.finrank A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI := ker_free σ v h
  rw [(kerEquiv σ v h).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem exists_form [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (y : M)
    (hy : y ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    ∃ σ : M →ₗ[A] A, σ y = 1 := by
  classical
  let e := Module.Free.chooseBasis A M
  by_cases h : ∀ i, e.repr y i ∈ IsLocalRing.maximalIdeal A
  · refine absurd ?_ hy
    rw [← e.sum_repr y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hu : IsUnit (e.repr y i) := by
      by_contra hn
      exact hi ((IsLocalRing.mem_maximalIdeal _).2 hn)
    obtain ⟨u, hu⟩ := hu
    refine ⟨((↑u⁻¹ : A)) • e.coord i, ?_⟩
    simp [← hu]

noncomputable def restr (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) :
    LinearMap.ker (σ ∘ₗ b) →ₗ[A] LinearMap.ker σ :=
  b.restrict (fun x hx => by simpa using hx)

theorem restr_coe (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x : LinearMap.ker (σ ∘ₗ b)) :
    (restr b σ x : M') = b x := rfl

theorem restr_proj (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M) (h : σ (b x₀) = 1) (q : M) :
    restr b σ (proj (σ ∘ₗ b) x₀ h q) = proj σ (b x₀) h (b q) :=
  Subtype.ext (by simp [restr_coe, proj_coe])

theorem lift_restr [IsLocalRing A] (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M)
    (h : σ (b x₀) = 1) (hb : Lift b) : Lift (restr b σ) := by
  intro J t hJ ht z hz
  obtain ⟨x, hx, hxz⟩ := hb J t hJ ht z (apply_mem_smul_top (LinearMap.ker σ).subtype _ hz)
  refine ⟨proj (σ ∘ₗ b) x₀ h x, ?_, ?_⟩
  · rw [restr_proj]
    exact apply_mem_smul_top (proj σ (b x₀) h) _ hx
  · have e : proj (σ ∘ₗ b) x₀ h x - z = proj (σ ∘ₗ b) x₀ h (x - z) := by
      rw [map_sub, proj_ker]
    rw [e]
    exact apply_mem_smul_top _ _ hxz

theorem generalized_inverse_of_lift_rank [IsLocalRing A] : ∀ (n : ℕ) (Q N : Type) [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (b : Q →ₗ[A] N), Module.finrank A N = n → Lift b →
    ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q N _ _ _ _ _ _ _ _ b hn hb
    by_cases h : ∀ q, b q ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)
    · refine ⟨0, ?_⟩
      rw [GlobalTheory.T.lift_reduction_zero_of_maximal A Q N b hb h]
      simp
    · push_neg at h
      obtain ⟨x₀, hx₀⟩ := h
      obtain ⟨σ, hσ⟩ := exists_form _ hx₀
      have hσ' : (σ ∘ₗ b) x₀ = 1 := hσ
      haveI := ker_finite σ (b x₀) hσ
      haveI := ker_free σ (b x₀) hσ
      haveI := ker_finite (σ ∘ₗ b) x₀ hσ'
      haveI := ker_free (σ ∘ₗ b) x₀ hσ'
      have hlt : Module.finrank A (LinearMap.ker σ) < n := by
        have := finrank_ker σ (b x₀) hσ
        omega
      obtain ⟨s₁, hs₁⟩ := ih _ hlt (LinearMap.ker (σ ∘ₗ b)) (LinearMap.ker σ) (restr b σ) rfl
        (lift_restr b σ x₀ hσ hb)
      refine ⟨σ.smulRight x₀ + (LinearMap.ker (σ ∘ₗ b)).subtype ∘ₗ s₁ ∘ₗ proj σ (b x₀) hσ, ?_⟩
      ext q
      have h1 : restr b σ (s₁ (restr b σ (proj (σ ∘ₗ b) x₀ hσ' q))) =
          restr b σ (proj (σ ∘ₗ b) x₀ hσ' q) := LinearMap.congr_fun hs₁ _
      rw [restr_proj] at h1
      have h2 := congrArg (Subtype.val) h1
      rw [restr_coe, proj_coe] at h2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, map_add,
        map_smul, Submodule.subtype_apply]
      rw [h2]
      abel

end GlobalTheory.CompanionTheory.PerfVB.GenInv

theorem GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift :
    ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
      [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N]
      (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b :=
  fun A Q N _ _ _ _ _ _ _ _ _ _ b hb =>
    GenInv.generalized_inverse_of_lift_rank (A := A) _ Q N b rfl hb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveInvTranspose
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open GlobalTheory.SplitPts

namespace GlobalTheory.CompanionTheory.CompConjPlace

section Rep

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem exists_embed_fin (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) :
    ∀ (r : ℕ) (N : Submodule ℂ X) (T : Fin r → X →ₗ[ℂ] V), (∀ g, ∀ z ∈ N, ρ g z ∈ N) → N ≠ ⊥ →
      (∀ j g x, T j (ρ g x) = τ g (T j x)) → (∀ z ∈ N, (∀ j, T j z = 0) → z = 0) →
      ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  intro r
  induction r with
  | zero =>
    intro N T _ hne _ hinj
    exact absurd ((Submodule.eq_bot_iff N).2 fun z hz => hinj z hz fun j => j.elim0) hne
  | succ r ih =>
    intro N T hN hne hT hinj
    by_cases hK : N ⊓ LinearMap.ker (T 0) = ⊥
    · obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ).1 hτ
      let S : N →ₗ[ℂ] V := (T 0).comp N.subtype
      have hker : ∀ z : N, S z = 0 → z = 0 := fun z hz => by
        have h : (z : X) ∈ N ⊓ LinearMap.ker (T 0) := ⟨z.2, hz⟩
        rw [hK] at h
        exact Subtype.ext h
      have hSinj : Function.Injective S := (injective_iff_map_eq_zero S).2 hker
      obtain ⟨z₀, hz₀, hz₀'⟩ := (Submodule.ne_bot_iff N).1 hne
      have hrange : LinearMap.range S = ⊤ := by
        refine (hirr (LinearMap.range S) ?_).resolve_left fun h => ?_
        · rintro g _ ⟨z, rfl⟩
          exact ⟨⟨ρ g z, hN g z z.2⟩, hT 0 g z⟩
        · have h0 : S ⟨z₀, hz₀⟩ = 0 := (Submodule.mem_bot ℂ).1 (h ▸ LinearMap.mem_range_self S ⟨z₀, hz₀⟩)
          exact hz₀' (congrArg Subtype.val (hker _ h0))
      let e : N ≃ₗ[ℂ] V := LinearEquiv.ofBijective S ⟨hSinj, LinearMap.range_eq_top.1 hrange⟩
      refine ⟨N.subtype ∘ₗ e.symm.toLinearMap, fun h => hz₀' ?_, fun g v => ?_⟩
      · have h1 := LinearMap.congr_fun h (e ⟨z₀, hz₀⟩)
        simpa using h1
      · have h1 : e.symm (τ g v) = ⟨ρ g (e.symm v), hN g _ (e.symm v).2⟩ := by
          rw [LinearEquiv.symm_apply_eq]
          change τ g v = T 0 (ρ g (e.symm v))
          rw [hT]
          exact congrArg (τ g) (e.apply_symm_apply v).symm
        change ((e.symm (τ g v) : N) : X) = _
        rw [h1]
        rfl
    · refine ih (N ⊓ LinearMap.ker (T 0)) (fun j => T j.succ) (fun g z hz => ⟨hN g z hz.1, ?_⟩) hK
        (fun j => hT j.succ) fun z hz h => hinj z hz.1 fun j => ?_
      · change T 0 (ρ g z) = 0
        rw [hT, show T 0 z = 0 from hz.2, map_zero]
      · refine Fin.cases hz.2 h j

theorem exists_embed (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) {ι : Type*}
    (T : ι → X →ₗ[ℂ] V) (hT : ∀ i g x, T i (ρ g x) = τ g (T i x)) (hinj : ∀ x, (∀ i, T i x = 0) → x = 0)
    (y : X) (hy : y ≠ 0) (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => T i y))) :
    ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  classical
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1
    (Module.Finite.iff_fg.1 hfd)
  have hidx : ∀ j : Fin s.card, ∃ i, T i y = (s.equivFin.symm j : V) := fun j =>
    hs (s.equivFin.symm j).2
  choose idx hidx using hidx
  have hmem : ∀ i, T i y ∈ Submodule.span ℂ (Set.range fun j => T (idx j) y) := fun i => by
    have h1 : T i y ∈ Submodule.span ℂ (s : Set V) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_mono ?_ h1
    intro x hx
    refine ⟨s.equivFin ⟨x, hx⟩, ?_⟩
    simp [hidx]
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem i)
  let N : Submodule ℂ X := ⨅ i, LinearMap.ker (T i - ∑ j, c i j • T (idx j))
  have hNmem : ∀ z, z ∈ N ↔ ∀ i, T i z = ∑ j, c i j • T (idx j) z := fun z => by
    simp [N, Submodule.mem_iInf, LinearMap.sum_apply, sub_eq_zero]
  refine exists_embed_fin ρ τ hτ s.card N (fun j => T (idx j)) (fun g z hz => ?_) ?_ (fun j => hT _)
    fun z hz h => hinj z fun i => ?_
  · rw [hNmem] at hz ⊢
    intro i
    simp only [hT, hz i, map_sum, map_smul]
  · refine (Submodule.ne_bot_iff N).2 ⟨y, (hNmem y).2 fun i => (hc i).symm, hy⟩
  · rw [(hNmem z).1 hz i]
    simp [h]

end Rep

section Global

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

abbrev sLoc (n : ℕ) (w : Pl E) : GLw n (conjSrc (conjE E) w) →* GLw n w :=
  GeneralLinearGroup.map (conjLoc (conjE E) w)

theorem continuous_sLoc (w : Pl E) : Continuous (sLoc n w) :=
  Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1)

theorem surjective_invTranspose (R : Type) [CommRing R] : Function.Surjective (invTranspose n R) :=
  fun g => ⟨invTranspose n R g, GlobalTheory.GelfandKazhdan.invTranspose_invTranspose n R g⟩

def conjRep (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := τ.ρ.comp (sLoc n w)
  smooth x := (τ.smooth x).preimage (continuous_sLoc w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective w) τ.irred

def conjDual (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := (conjRep τ).ρ.comp (invTranspose n _)
  smooth x := ((conjRep τ).smooth x).preimage (GlobalTheory.GelfandKazhdan.continuous_invTranspose n _)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (surjective_invTranspose _) (conjRep τ).irred

theorem isLocComp_conjDual (π : CuspSub E n) (hπ : GlobalTheory.ContraPair.DualIsConj π) {τ : SmIrr (GLw n w)}
    (hτ : π.IsLocComp w τ) : π.IsLocComp (conjSrc (conjE E) w) (conjDual τ) := by
  obtain ⟨B, hL, -, hB, -⟩ := hπ
  have hadm : ∀ σ : SmIrr (GLw n (conjSrc (conjE E) w)), IsAdmissible σ.ρ := fun σ =>
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨e⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n (conjRep τ).V (conjRep τ).ρ (hadm _) (conjRep τ).irred
  have hloc : IsLocCompGL π.V w τ := by
    obtain ⟨f, h0, hf⟩ := hτ
    refine ⟨π.V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => ?_⟩
    exact congrArg Subtype.val (hf g v)
  let Bf (f : GlobalTheory.LocDual.Maps π.V w τ) : (conjRep τ).V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ :=
    B.flip.comp (f.1.codRestrict π.V f.2.1)
  have hBf : ∀ f g a ψ, Bf f ((conjRep τ).ρ g a) (π.locRep (conjSrc (conjE E) w) g ψ) = Bf f a ψ := by
    intro f g a ψ
    have h1 : f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a) =
        π.op (.fin (GeneralLinearGroup.map (conjFin (conjE E)) (locGL E n _ g))) (f.1.codRestrict π.V f.2.1 a) := by
      refine Subtype.ext ?_
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL]
      exact f.2.2 _ a
    change B (π.locRep _ g ψ) (f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a)) = B ψ (f.1.codRestrict π.V f.2.1 a)
    rw [h1, CuspSub.locRep_eq]
    exact hB _ ψ _
  let P (f : GlobalTheory.LocDual.Maps π.V w τ) := GlobalTheory.InvPairing.pairMap (conjRep τ).ρ (π.isSmooth_locRep _) (Bf f) (hBf f)
  let T (f : GlobalTheory.LocDual.Maps π.V w τ) : π.V →ₗ[ℂ] (conjDual τ).V := e.symm.toLinearEquiv.toLinearMap ∘ₗ (P f).toLinearMap
  have hT : ∀ f g ψ, T f (π.locRep _ g ψ) = (conjDual τ).ρ g (T f ψ) := fun f g ψ => by
    have h1 := LinearMap.congr_fun ((P f).isIntertwining' g) ψ
    change e.symm.toLinearEquiv ((P f).toLinearMap (π.locRep _ g ψ)) = _
    rw [show (P f).toLinearMap (π.locRep _ g ψ) = _ from h1]
    exact GlobalTheory.ConjPairLoc.equiv_apply e.symm g _
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff π.V).1 π.ne_bot
  obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.SqIntUnit.compactOpen_basis _ n _
    ((π.isSmooth_locRep (conjSrc (conjE E) w) ⟨y, hy⟩).mem_nhds (by simp))
  haveI := (hadm (conjDual τ)).2 K hKo hKc
  have hle : Submodule.span ℂ (Set.range fun f => T f ⟨y, hy⟩) ≤ fixed (conjDual τ).ρ K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine LocEx.mem_fix.2 fun k hk => ?_
    change (conjDual τ).ρ k (T f ⟨y, hy⟩) = T f ⟨y, hy⟩
    rw [← hT, show π.locRep _ k ⟨y, hy⟩ = ⟨y, hy⟩ from hK hk]
  have hfd := Submodule.finiteDimensional_of_le hle
  have hinj : ∀ ψ, (∀ f, T f ψ = 0) → ψ = 0 := fun ψ hψ => by
    by_contra hne
    have hβ : B ψ ≠ 0 := fun h => hne (hL ψ fun φ => LinearMap.congr_fun h φ)
    obtain ⟨f, hf⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred w τ hloc (B ψ) hβ
    refine hf (LinearMap.ext fun a => ?_)
    have h1 : (P f).toLinearMap ψ = 0 := e.symm.toLinearEquiv.map_eq_zero_iff.1 (hψ f)
    exact LinearMap.congr_fun (congrArg Subtype.val h1) a
  obtain ⟨Φ, h0, hΦ⟩ := exists_embed (π.locRep _) (conjDual τ).ρ (conjDual τ).irred T hT hinj ⟨y, hy⟩
    (fun h => hy0 (congrArg Subtype.val h)) hfd
  exact ⟨Φ, h0, hΦ⟩

end Global

end GlobalTheory.CompanionTheory.CompConjPlace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  intro X _ q σ D c W h g hg
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · have ht : c.e.target = ∅ := by rw [← c.e.image_source_eq_target, hs, Set.image_empty]
    simp [ht]
  have sectionFrameQuotient := mem_ptsIn.1 (c.source_subset hy0)
  haveI : Nonempty c.U := ⟨⟨_, sectionFrameQuotient⟩⟩
  have hgU : genericPoint X ∈ c.U := gen_mem sectionFrameQuotient
  haveI := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (fnOf W h g)
  have hal : ∀ t : Γ(X, c.U), algebraMap Γ(X, c.U) X.functionField t = fnOf c.U hgU t :=
    fun _ => rfl
  rw [hal, hal] at hab
  have hb0 : fnOf c.U hgU b ≠ 0 := fun e =>
    nonZeroDivisors.ne_zero hb ((map_eq_zero_iff _ (fnOf_injective _ _)).1 e)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg
    rw [← hab, map_zero, zero_div]
  have hrel : fnOf W h g * fnOf c.U hgU b = fnOf c.U hgU a := by
    rw [← hab, div_mul_cancel₀ _ hb0]
  have hI : genericPoint X ∈ W ⊓ c.U := ⟨h, hgU⟩
  have hres : resG X (inf_le_left : W ⊓ c.U ≤ W) g * resG X (inf_le_right : W ⊓ c.U ≤ c.U) b =
      resG X (inf_le_right : W ⊓ c.U ≤ c.U) a := by
    apply fnOf_injective _ hI
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG]
    exact hrel
  obtain ⟨Q, hQ, r, hQr⟩ := GlobalTheory.ChernNull.exists_poly_dvd _ c.etale a ha0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (RingHom.injective_int σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (GlobalTheory.ChernNull.volume_poly_zero D _ hP)
  rintro v ⟨hv, hyW, hyz⟩
  have hys : c.e.symm v ∈ c.e.source := c.e.map_target hv
  have hyU := c.source_subset hys
  have hyI : c.e.symm v ∈ ptsIn q σ (W ⊓ c.U) := mem_ptsIn_inf.2 ⟨hyW, hyU⟩
  have hay : ev q σ c.U a (c.e.symm v) = 0 := by
    rw [← ev_res inf_le_right hyI, ← hres, ev_mul, ev_res inf_le_left hyI, hyz, zero_mul]
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun i => c.e (c.e.symm v) i) := by
    refine MvPolynomial.ringHom_ext (fun i => ?_) (fun i => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq _ hys]
  have hQy := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at hQy
  show MvPolynomial.eval (fun i => v i) (MvPolynomial.map σ Q) = 0
  rw [c.e.right_inv hv] at hQy
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← hQy, hQr, map_mul, ← ev_eq hyU, hay,
    zero_mul]
end

