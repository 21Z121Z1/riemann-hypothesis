import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseVar

open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem j_mem_range_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Xo.XF c) :
    Y.j x ∈ Set.range X.π := by
  let xF : Sp ((Xo.XF c).residueField x) ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField x
  letI : Algebra c.F ((Xo.XF c).residueField x) := (Spec.preimage (xF ≫ pullback.snd _ _)).hom.toAlgebra
  have hsnd : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F ((Xo.XF c).residueField x)) :=
    (Spec.map_preimage _).symm
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frPt (S := (Xo.XF c).residueField x) (Xo := Xo) (c := c)
    (xF ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, sOf, ← Spec.map_comp]; rfl)
  have hx : xF = GlobalTheory.FlagMod.frX P := GlobalTheory.FlagMod.eq_frX P hP.symm hsnd
  let pt : Sp ((Xo.XF c).residueField x) := IsLocalRing.closedPoint _
  refine ⟨X.ptY P pt, ?_⟩
  have e1 : X.π (X.ptY P pt) = (X.ptY P ≫ X.π) pt := (Scheme.Hom.comp_apply _ _ _).symm
  rw [e1, (X.lies_ptY P).1, ← hx, Scheme.Hom.comp_apply]
  exact congrArg Y.j (Scheme.fromSpecResidueField_apply x _)

theorem surjective_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Function.Surjective X.π := by
  have := X.proper
  have hc : IsClosed (Set.range X.π) := X.π.isClosedMap.isClosed_range
  have hd : closure (Set.range Y.j) ⊆ Set.range X.π :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact j_mem_range_π X x) hc
  exact fun y => hd (LogKS.dense_interior Y y)

theorem surjective_π₀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) :
    Function.Surjective (π₀ X Z) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_π X ((barComp Y Z).ι y)
  have hzU : z ∈ X.π ⁻¹ᵁ barComp Y Z := by
    show X.π z ∈ barComp Y Z
    have : (barComp Y Z).ι y ∈ Set.range (barComp Y Z).ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι, ← hz] at this
  obtain ⟨z', hz'⟩ : z ∈ Set.range (inc₀ X Z) := by rwa [Scheme.Opens.range_ι]
  refine ⟨z', (barComp Y Z).ι.isOpenEmbedding.injective ?_⟩
  have e1 := Scheme.Hom.comp_apply (π₀ X Z) (barComp Y Z).ι z'
  have e2 := Scheme.Hom.comp_apply (inc₀ X Z) X.π z'
  rw [morphismRestrict_ι] at e1
  rw [← e1, e2, hz', hz]

theorem exists_var (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed Xo c) :
    ∃ (B : GlobalTheory.ProjVar.Var c.F) (φ : B.X ⟶ X₀ TF.Y Z), IsIso φ ∧ φ ≫ s₀ TF.Y Z = B.str ∧ B.dim = Dw.dim := by
  have hsm := GlobalTheory.VarFlag.smooth_gen TF.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) TF.Y c.F (RingEquiv.refl _) hF hsm
  have hJ : ∀ w : gen TF.Y, genι TF.Y w ∈ barComp TF.Y Z ↔ w ∈ Set.range (j Z) :=
    GlobalTheory.VarFlag.barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have := (hB Z).1
  have hr : Set.range (j Z ≫ genι TF.Y) ⊆ Set.range (barComp TF.Y Z).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨b, rfl⟩
    exact (hJ _).2 ⟨b, rfl⟩
  let φ := IsOpenImmersion.lift (barComp TF.Y Z).ι (j Z ≫ genι TF.Y) hr
  have hφ : φ ≫ (barComp TF.Y Z).ι = j Z ≫ genι TF.Y := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (φ ≫ (barComp TF.Y Z).ι) := by rw [hφ]; infer_instance
  have : IsOpenImmersion φ := IsOpenImmersion.of_comp φ (barComp TF.Y Z).ι
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, genι TF.Y w = (barComp TF.Y Z).ι y :=
      ⟨inv (genι TF.Y) ((barComp TF.Y Z).ι y), by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hm : genι TF.Y w ∈ barComp TF.Y Z := by
      have : (barComp TF.Y Z).ι y ∈ Set.range (barComp TF.Y Z).ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι, ← hw] at this
    obtain ⟨b, rfl⟩ := (hJ w).1 hm
    refine ⟨b, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, hw]
  have hiso : IsIso φ := (isIso_iff_isOpenImmersion_and_surjective φ).2 ⟨inferInstance, ⟨hsurj⟩⟩
  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  refine ⟨B Z, φ, hiso, ?_, (hB Z).2.1⟩
  have h3 := (hB Z).2.2.1
  rw [hspid, Category.comp_id] at h3
  rw [← h3, GlobalTheory.VarFlag.genStr_eq, s₀, ← Category.assoc, hφ, Category.assoc]

theorem isVariety_barComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  intro E _ _ _ H Dw l Xo c TF Z hF
  obtain ⟨B, φ, hφ, hs, hd⟩ := exists_var TF Z hF
  have hs' : s₀ TF.Y Z = inv φ ≫ B.str := by rw [← hs, IsIso.inv_hom_id_assoc]
  have : Nonempty (X₀ TF.Y Z) := ⟨φ (genericPoint B.X)⟩
  have hint : IsIntegral (X₀ TF.Y Z) := isIntegral_of_isOpenImmersion (inv φ)
  refine ⟨hint, ?_, ?_, ?_, ⟨surjective_π₀ TF.X Z⟩, ?_, ?_⟩
  · rw [hs', ← hd]
    exact GlobalTheory.VarFlag.smooth_iso _ _ B.smooth
  · obtain ⟨N, i, hi, hs2⟩ := B.isProjOver
    exact ⟨N, inv φ ≫ i, inferInstance, by rw [Category.assoc, hs2, hs']⟩
  · rw [hs']
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (inv φ) (inv φ ≫ B.str) B.str (𝟙 _)) inferInstance
  · haveI : GlobalTheory.IsNormalScheme TF.Y.X := GlobalTheory.IsNormalScheme.of_pred TF.Y.normal
    exact GlobalTheory.IsNormalScheme.of_isOpenImmersion (i₀ TF.Y Z ≫ TF.Y.j)
  · intro v hv
    have : IsOpenImmersion (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) := by rw [j₀_ι]; infer_instance
    have : IsOpenImmersion (j₀ TF.Y Z) := IsOpenImmersion.of_comp _ (barComp TF.Y Z).ι
    have hgen : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
      have hirr : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
      exact IsIrreducible.isGenericPoint_genericPoint hirr (isClosed_of_mem_irreducibleComponents _ Z.2)
    have hsub : Set.range (j₀ TF.Y Z) ⊆ closure {j₀ TF.Y Z v} := by
      rintro _ ⟨w, rfl⟩
      have hw : i₀ TF.Y Z w ∈ (Z : Set (Xo.XF c)) := (j_mem_barComp (Y := TF.Y) Z _).1 w.2
      have h1 : i₀ TF.Y Z v ⤳ i₀ TF.Y Z w := hv ▸ hgen.specializes hw
      have h2 : v ⤳ w := (i₀ TF.Y Z).isOpenEmbedding.isInducing.specializes_iff.1 h1
      exact specializes_iff_mem_closure.1 (h2.map (j₀ TF.Y Z).continuous)
    have hdense : Dense (Set.range (j₀ TF.Y Z)) :=
      (j₀ TF.Y Z).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, rfl⟩⟩
    have hg : IsGenericPoint (j₀ TF.Y Z v) (Set.univ : Set (X₀ TF.Y Z)) := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← hdense.closure_eq]
      exact closure_minimal hsub isClosed_closure
    exact hg.eq (genericPoint_spec (X₀ TF.Y Z))

end GlobalTheory.BaseVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isHomeomorph_bcPt (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0})
    (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) :
    IsHomeomorph (bcPt hp.w τ) := by
  let E : CxPts q τ ≃ CxPts p (τ.comp ρ) := Equiv.ofBijective (bcPt hp.w τ) (CxPts.bijective_bcMap hp τ)
  have hm : ∀ z, (bcPt hp.w τ z).1 = z.1 ≫ j := fun _ => rfl
  have hE : ∀ y, bcPt hp.w τ (E.symm y) = y := E.apply_symm_apply
  have hc : Continuous E.symm := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨U, hyU⟩ := CxPts.exists_mem_ptsIn (iSup_affineOpens_eq_top X) y
    have hU : IsAffineOpen U.1 := U.2
    have hW : IsAffineOpen (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := by
      rw [show j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤ = j ⁻¹ᵁ U.1 from inf_top_eq _]
      exact GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback hp hU
    have hin : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := fun w hw =>
      mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (by rw [hE]; exact hw), mem_ptsIn_top⟩
    have hnb : ptsIn p (τ.comp ρ) U.1 ∈ 𝓝 y := (isOpen_ptsIn _).mem_nhds hyU
    have hev : ∀ᶠ w in 𝓝 y, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := eventually_of_mem hnb hin
    letI := ρ.toAlgebra
    have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout (isPushout_sections p q j hp U.1 hU)
    refine tendsto_subtype_rng.2 ((Points.tendsto_iff_of_generators hW (hin y hyU) hgen).2 ⟨hev, ?_⟩)
    rintro f (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, ev p (τ.comp ρ) U.1 a w =
          valR (E.symm w).1 _ ((j.appLE U.1 (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom a) := fun w hw => by
        have := CxPts.ev_appLE_of_comp hm inf_le_left a (hin w hw)
        rw [hE] at this
        exact this.symm
      have h := ((continuousOn_ev a).continuousAt hnb).tendsto
      rw [e y hyU] at h
      exact h.congr' (eventually_of_mem hnb e)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, τ b =
          valR (E.symm w).1 _ (algX q (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) b) := fun w hw => (ev_algX (hin w hw) b).symm
      have h : Tendsto (fun _ : CxPts p (τ.comp ρ) => τ b) (𝓝 y) (𝓝 (τ b)) := tendsto_const_nhds
      have h' := h.congr' (eventually_of_mem hnb e)
      rw [e y hyU] at h'
      exact h'
  exact (Homeomorph.mk E (continuous_bcPt hp.w τ) hc).isHomeomorph

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_linMap_of_periods {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D₁ D₂ : PLat O bar) (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) (hP' : ∀ (a : O) x, P' (a • x) = ρ a *ᵥ P' x)
    (hinj : Function.Injective P') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hr : ∀ x, ∃ y, P' y = h (P x))
    (hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z) :
    ∃ w : D₁.La →ₗ[O] D₂.La, ∀ x, P' (w x) = h (P x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply hinj
    rw [map_add, hf, hf, hf, map_add, map_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, hP', hf, hf, hP, hc]

theorem int_eq_of_exp_eq (m n : ℤ)
    (H : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set k : ℕ := (n - m).natAbs + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (H k hk)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have E : ((n - m : ℤ) : ℂ) = ((j * k : ℤ) : ℂ) := by
    push_cast
    field_simp at hj
    linear_combination hj
  have E' : n - m = j * k := by exact_mod_cast E
  have hd : (k : ℤ) ∣ n - m := ⟨j, by rw [E', mul_comm]⟩
  have h0 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by rw [Int.natAbs_natCast]; omega)
  omega

theorem unifAt_cmp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e e' hN U1 U2
  obtain ⟨-, hper1, hexp1, hker1, hact1, hweil1, heta1⟩ := U1
  obtain ⟨-, hper2, hexp2, hker2, hact2, hweil2, heta2⟩ := U2
  have lift := fun (e₁ e₂ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (α : F.A ⟶ F.A) (h1 : IsExp y e₁) (h2 : IsExp y e₂)
    (hα : IsMonHom α) => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism F.X F.A g F.ab F.dim y e₁ e₂ α h1 h2 hα
  obtain ⟨M, hM, -⟩ := lift e e' (𝟙 _) hexp1 hexp2 inferInstance
  obtain ⟨M', hM', -⟩ := lift e' e (𝟙 _) hexp2 hexp1 inferInstance
  simp only [Category.comp_id] at hM hM'
  have h1 : M'.comp M = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e e (𝟙 _) hexp1 hexp1 inferInstance
    rw [hK (M'.comp M) (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  have h2 : M.comp M' = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e' e' (𝟙 _) hexp2 hexp2 inferInstance
    rw [hK (M.comp M') (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M M' h2 h1
  have hh : ∀ z, e' (h z) = e z := hM
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ P'.range := fun z => by rw [← hker1, ← hker2, hh]
  have hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    obtain ⟨K, -, hK⟩ := lift e e' (F.act a) hexp1 hexp2 (F.hom a)
    have k1 := hK ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (Matrix.mulVecLin (ρ a)))
      (fun z => by simp [hh, hact1])
    have k2 := hK ((Matrix.mulVecLin (ρ a)).comp (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))
      (fun z => by simp [hact2, hh])
    have := congrArg (fun f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) => f z) (k1.trans k2.symm)
    simpa using this
  have hc' : ∀ (a : O) z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    apply h.injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨w₁, hw₁⟩ := exists_linMap_of_periods ρ D' D'' P P' hper1.1 hper2.1 hper2.2.1 h
    (fun x => (AddMonoidHom.mem_range).mp ((hrange (P x)).mp ⟨x, rfl⟩)) hc
  obtain ⟨w₂, hw₂⟩ := exists_linMap_of_periods ρ D'' D' P' P hper2.1 hper1.1 hper1.2.1 h.symm
    (fun x => (AddMonoidHom.mem_range).mp ((hrange _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact ⟨x, rfl⟩))) hc'
  let w : D'.La ≃ₗ[O] D''.La := LinearEquiv.ofLinear w₁ w₂
    (LinearMap.ext fun x => hper2.2.1 (by simp [hw₁, hw₂]))
    (LinearMap.ext fun x => hper1.2.1 (by simp [hw₁, hw₂]))
  have hw : ∀ x, P' (w x) = h (P x) := hw₁
  refine ⟨w, h, ⟨?_, ?_⟩, hw, hh⟩
  · intro x x'
    refine (int_eq_of_exp_eq _ _ fun k hk => ?_)
    have H1 := hweil1 k x x' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have H2 := hweil2 k (w x) (w x') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hw, hw, ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hh, hh] at H2
    have := GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g F.ab F.dim F.L F.isLB y k _ _ _ _ H2 H1
    simpa using congrArg Units.val this
  · intro a
    have e0 : e' 0 = 1 := (hker2 0).mpr (zero_mem _)
    set v := (N : ℂ)⁻¹ • P' (t' a)
    set u := (N : ℂ)⁻¹ • P' (w (t a)) - v
    have huv : e' (u + v) = e' v := by
      rw [sub_add_cancel, hw, ← LinearEquiv.map_smul, hh, ← heta1, heta2]
    have hu : e' u = 1 := by
      have := (hexp2.1 (u + v) (-v)).symm
      rw [add_neg_cancel_right, huv, ← hexp2.1, add_neg_cancel, e0] at this
      exact this.symm
    obtain ⟨x₀, hx₀⟩ := (hker2 u).mp hu
    refine ⟨x₀, ?_⟩
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    apply hper2.2.1
    have : P' (w (t a)) - P' (t' a) = (N : ℂ) • u := by
      simp only [u, v, ← smul_sub, smul_smul, mul_inv_cancel₀ hN', one_smul]
    rw [map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hx₀, ← this]
    abel

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotential
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntAlter

open Set

variable {k : Type} [CommRing k] {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] {q : Y ⟶ Sp k}
  {σ : k →+* ℂ}

theorem continuousOn_logNorm {L : LB Y} (φ : Weight q σ L) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hφ : φ.IsCInf) :
    ContinuousOn (logNorm φ r) (offSupp q σ (divOfRatSec φ.isLB hr)) := by
  intro y hy
  have ho := isOpen_offSupp (q := q) (σ := σ) (divOfRatSec φ.isLB hr)
  have hi : y ∈ ptsIn q σ (L.U (pick φ.isLB y)) := mem_pick _ y
  have hu := hr.unitAt φ.isLB hy hi
  have hn : ptsIn q σ (L.U (pick φ.isLB y)) ∩ offSupp q σ (divOfRatSec φ.isLB hr) ∈ 𝓝 y :=
    inter_mem ((isOpen_ptsIn _).mem_nhds hi) (ho.mem_nhds hy)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun z => Real.log ‖ratVal (r (pick φ.isLB y) : Y.functionField) z‖ -
      φ.φ (pick φ.isLB y) z / 2) y :=
    ((LogNormInt.continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ _ y hi).continuousAt.div_const 2)
  refine hc.congr ?_
  filter_upwards [hn] with z hz
  exact (logNorm_eq φ hr hz.2 hz.1).symm

variable (M : HermLB q) (ρ : Y' ⟶ Y) (hη : ρ (genericPoint Y') ⤳ genericPoint Y)
  {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)

theorem mem_offSupp_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    y ∈ offSupp (ρ ≫ q) σ ((M.restr ρ).div (MultPull.isRatSec_pull_map ρ hη hr)) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  obtain ⟨c, hc⟩ := exists_chart (M.restr ρ).isLB (under y)
  have hc' : PtsOver.map ρ rfl _ y ∈ ptsIn q σ (M.B.U (c PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hu := hr.unitAt M.isLB hx hc'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  exact mem_offSupp.2 fun h => ((presents_divOfRatSec (M.restr ρ).isLB
    (MultPull.isRatSec_pull_map ρ hη hr)).isEqn c _ hc).mem_supp_iff.1 h hu'

theorem logNorm_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    logNorm ((M.restr ρ).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (c PUnit.unit))) y = logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  have hj : y ∈ ptsIn _ σ ((M.restr ρ).B.U (pick ((M.restr ρ).φ σ).isLB y)) := mem_pick _ y
  have hj' : PtsOver.map ρ rfl _ y ∈
      ptsIn q σ (M.B.U (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hj) PUnit.unit)
  have hu := hr.unitAt M.isLB hx hj'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  have e₁ : ((M.restr ρ).φ σ).φ (pick ((M.restr ρ).φ σ).isLB y) y =
      (M.φ σ).φ (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) (PtsOver.map ρ rfl _ y) :=
    (M.φ σ).pull_φ ρ rfl _ y
  have e₂ : ratVal ((Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) : Y'.functionFieldˣ) : Y'.functionField) y =
      ratVal (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) : Y.functionField)
      (PtsOver.map ρ rfl _ y) := by
    show ratVal (TrueGeo.SmallSec.fnMap ρ hη (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) :
      Y.functionField)) y = _
    rw [TrueGeo.SmallSec.ratVal_eq_valAt y hu'.regAt, TrueGeo.SmallSec.valAt_fnMap ρ hη _ hu.regAt,
      TrueGeo.SmallSec.ratVal_eq_valAt _ hu.regAt]
    rfl
  rw [logNorm_eq (M.φ σ) hr hx hj', logNorm, e₁, e₂]

end GlobalTheory.ArchIntAlter

namespace GlobalTheory.ArchIntAlter

open Set

theorem archIntegrable : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hRA k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', _, ρ, hreg, hgen, hdeg⟩ := GlobalTheory.T.exists_regular_alteration_arithmetic hRA k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hgen ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := LogNormInt.archIntegrable hreg (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy => mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy => logNorm_pull M ρ hη hr hy
  exact GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite k Y q e hY Y' ρ hreg.toIsArithVar hgen hdeg N σ _ _
    (continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntAlter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOmegaFormEqC2SubC1ProductStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_omega_form_eq_c2_sub_c1_product : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) = fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) := by
  first | exact @GlobalTheory.LineForm.ddc_omF_eq | exact GlobalTheory.LineForm.ddc_omF_eq | (intros; apply GlobalTheory.LineForm.ddc_omF_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeOneClassPullbackOfCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  first | exact @GlobalTheory.PDForm.isPull1_of_pair_coboundary | exact GlobalTheory.PDForm.isPull1_of_pair_coboundary | (intros; apply GlobalTheory.PDForm.isPull1_of_pair_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeTwoClassPullbackOfCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s)), Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1 → Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1 → IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  first | exact @GlobalTheory.PDForm.PullTwo.isPull2_of_coboundary | exact GlobalTheory.PDForm.PullTwo.isPull2_of_coboundary | (intros; apply GlobalTheory.PDForm.PullTwo.isPull2_of_coboundary <;> assumption)
end

