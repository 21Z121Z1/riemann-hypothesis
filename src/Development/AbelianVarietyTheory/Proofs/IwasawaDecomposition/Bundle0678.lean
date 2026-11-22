import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := GlobalTheory.T.projective_bundle_points_of_rational_model F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, GlobalTheory.T.geometricallyIntegral_of_affCover F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, GlobalTheory.T.isFlagRefinementBundle_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := GlobalTheory.T.exists_graded_line_divisors_full_flag E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

theorem nonempty_flagTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z) → Nonempty (FlagTor Z e U) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U hσ hU hne hF hsm hS
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c O β Z F e hF hsm
  have key := fun i : U.Comp =>
    haveI := (hB (q i)).1
    exists_flagCpt Z e hS (B (q i)) (j (q i)) (hB (q i)).2.2.1
  choose C f hπ hdim hl using key
  have lift : ∀ (K : Type) [Field K] (x : Sp K ⟶ gen Z) (i : Comp Xo c),
      x (IsLocalRing.closedPoint K) ∈ Set.range (j i) → ∃ x' : Sp K ⟶ (B i).X, x' ≫ j i = x := fun K _ x i h => by
    have := (hB i).1
    refine ⟨IsOpenImmersion.lift (j i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨w, rfl⟩
    rwa [show w = IsLocalRing.closedPoint K from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  refine ⟨⟨C, fun k => ?_, fun K _ _ χ x hx g => ?_, fun i x s => ?_⟩⟩
  · rw [hdim, (hB _).2.1, GlobalTheory.T.flag_space_dimension_eq_sum_choose E H Dw, hU.1]
  · obtain ⟨i₀, hi, hi'⟩ := hcov (x (IsLocalRing.closedPoint K))
    obtain ⟨i, rfl⟩ := q.surjective i₀
    obtain ⟨x', hx'⟩ := lift K x _ hi
    obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hl i K χ x x' hx' hx g
    refine ⟨⟨i, p⟩, ⟨by rw [hπ, ← Category.assoc, hp1, hx'], hp2⟩, ?_⟩
    rintro ⟨i', p'⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    rw [hπ, ← Category.assoc] at h1
    obtain rfl : i' = i := q.injective (hi' _ ⟨(p' ≫ f i') (IsLocalRing.closedPoint K), by
      rw [← h1]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩)
    have := (hB (q i')).1
    rw [hp3 p' ⟨(cancel_mono (j (q i'))).1 (h1.trans hx'.symm), h2⟩]
  · let x₀ : Sp ℂ ⟶ gen Z := (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un i x) ≫ Z.jQ :)
    have hx₀ : x₀ ≫ genStr Z = spMap σ :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _))
    obtain ⟨x', hx'⟩ := lift ℂ x₀ (q i) ((hB _).2.2.2 _ (hq i x _))
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z _ _ x₀ hx₀
    obtain ⟨p, ⟨hp1, -⟩, -⟩ := hl i _ _ x₀ x' hx' hx₀ g
    have : p ≫ (C i).π = x₀ := by rw [hπ, ← Category.assoc, hp1, hx']
    exact ⟨p s, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp ℂ ⟶ gen Z => t s) this)⟩

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chart_theta_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ (κ : ℂ) (r : PowerSeries ℂ) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), κ ≠ 0 ∧ PowerSeries.constantCoeff r ≠ 0 ∧ IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧ ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * ((κ * rw) * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hL2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨hA, hB⟩ := GlobalTheory.theta_generates_along_arc hL.globalFns hL.secBaseChange Y a χ W
  have hw0 : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I : ℂ).im := by simp
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hs, hp⟩ := Θ.pos _ hw0
    have h7 := (GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic g Θ.S (Θ.τ ((Ha.T + 1 : ℝ) * Complex.I)) Θ.c₁ Θ.c₂ hs hp Θ.half₁ Θ.half₂ Θ.c₁_S).1
    apply h7
    funext v
    set w := ((Ha.T + 1 : ℝ) * Complex.I : ℂ) with hwdef
    have hz : Θ.h.mulVec (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v).symm
    rw [← hz]
    generalize (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = z
    obtain ⟨fr, -, n, -, -, hv⟩ := Θ.onB w hw0
    obtain ⟨j, hj⟩ := exists_chart a.D₀.P.isLB ((show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (IsLocalRing.closedPoint ℂ))
    have hU : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ a.D₀.P.L.U j := fun q _ =>
      (Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) q) ▸ hj
    have e := hv j z hU
    have e0 : valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (a.D₀.P.L.U j) (th.f j) = 0 := by
      rw [hc j]
      exact (dif_pos hU).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    rw [e0] at e
    have := (mul_eq_zero.1 e.symm).resolve_right (n j z hU)
    exact (mul_eq_zero.1 this).resolve_left Θ.κ_ne
  have hth : GlobalTheory.ArcQ.ThNZ th := ((GlobalTheory.ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ th).1).1 hne
  obtain ⟨⟨t, ht, -⟩, hnz⟩ := hB th
  obtain ⟨σ0, fam, hfam0, hexp, -, -, -, -, ⟨w₂, hw₂⟩, hrest⟩ := hA t (hnz t ht hth _)
  have hpull : GlobalTheory.ThetaUnit.IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) := hfam0 ▸ ht
  obtain ⟨-, hr⟩ := (hrest w₂ hw₂.1).2 hPI
  obtain ⟨r, hr⟩ := hr M.U M.θ hM ⟨M.θ_mem, M.gen⟩
  obtain ⟨w₀, h₀⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m0.toSABMap
  obtain ⟨w₁, h₁⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m
  obtain ⟨fr₀, hfr₀⟩ := Θ.frame _ hw0
  obtain ⟨κ, hκ, -, -, hmain⟩ := Ha.theta th σ0 fam Θ.bas Θ.S Θ.h Θ.τ Θ.c₁ Θ.c₂ w₂ w₁ w₀ hne hexp hpull Θ.sympl Θ.ker Θ.per Θ.half₁ Θ.half₂ hw₂ h₁ h₀ ⟨_, fr₀, hw0, hfr₀⟩
  obtain ⟨T', hT'⟩ := hmain M.U M.θ r.val hM M.θ_mem hr
  refine ⟨κ, r.val, w₀, w₁, hκ, ?_, h₀, h₁, T', hT'⟩
  exact ((PowerSeries.isUnit_iff_constantCoeff).1 r.isUnit).ne_zero

theorem exists_bounds_of_sumsAt : ∀ (κ : ℂ), κ ≠ 0 → ∀ r : PowerSeries ℂ, PowerSeries.constantCoeff r ≠ 0 → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ rw : ℂ, SumsAt r w rw → C⁻¹ ≤ ‖κ * rw‖ ∧ ‖κ * rw‖ ≤ C := by
  intro κ hκ r hr0
  by_cases hex : ∃ w₀ rw₀, SumsAt r w₀ rw₀
  swap
  · exact ⟨0, 1, one_pos, fun w _ rw h => (hex ⟨w, rw, h⟩).elim⟩
  obtain ⟨w₀, rw₀, h₀⟩ := hex
  have hq₀ : 0 < ‖eTwoPi w₀‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖PowerSeries.coeff n r * eTwoPi w₀ ^ n‖ ≤ B := by
    obtain ⟨B, hB⟩ := h₀.summable.tendsto_atTop_zero.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have ha₀ : 0 < ‖PowerSeries.constantCoeff r‖ := norm_pos_iff.2 hr0
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set A := ‖PowerSeries.constantCoeff r‖ with hA
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  set t : ℝ := min (1 / 2) (A / (4 * B')) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos ha₀ (by linarith))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htB : t ≤ A / (4 * B') := min_le_right _ _
  have htB' : 4 * B' * t ≤ A := by
    have := mul_le_mul_of_nonneg_left htB (by linarith : (0:ℝ) ≤ 4 * B')
    rwa [mul_div_cancel₀ _ (by linarith : (4 * B' : ℝ) ≠ 0)] at this
  refine ⟨-Real.log (t * ‖eTwoPi w₀‖) / (2 * Real.pi), max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)),
    lt_max_of_lt_left (by positivity), fun w hw rw hrw => ?_⟩
  have hqn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    simp [eTwoPi, Complex.norm_exp]
  have hq : ‖eTwoPi w‖ ≤ t * ‖eTwoPi w₀‖ := by
    rw [hqn]
    have hpos : 0 < t * ‖eTwoPi w₀‖ := mul_pos ht0 hq₀
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 hw
    linarith
  have hf := (hasSum_nat_add_iff' 1).2 hrw
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  have hg : HasSum (fun n : ℕ => B' * t * t ^ n) (B' * t * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0.le (by linarith)).mul_left (B' * t)
  have hle : ‖rw - PowerSeries.constantCoeff r‖ ≤ B' * t * (1 - t)⁻¹ := by
    refine hf.norm_le_of_bounded hg fun n => ?_
    have h1 : ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1) ≤ B' := by
      have := hB (n + 1)
      rw [norm_mul, norm_pow] at this
      exact this.trans (le_max_left _ _)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w‖ ^ (n + 1)
        ≤ ‖PowerSeries.coeff (n + 1) r‖ * (t * ‖eTwoPi w₀‖) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (norm_nonneg _)
      _ = (‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1)) * t ^ (n + 1) := by ring
      _ ≤ B' * t ^ (n + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = B' * t * t ^ n := by ring
  have h2 : B' * t * (1 - t)⁻¹ ≤ A / 2 := by
    have h1t : 0 < 1 - t := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ h1t]
    nlinarith
  have hlo : A / 2 ≤ ‖rw‖ := by
    have := norm_sub_norm_le (PowerSeries.constantCoeff r) rw
    rw [norm_sub_rev] at this
    linarith
  have hhi : ‖rw‖ ≤ 3 / 2 * A := by
    have := norm_sub_norm_le rw (PowerSeries.constantCoeff r)
    linarith
  rw [norm_mul]
  constructor
  · have hx : 0 < ‖κ‖ * A := mul_pos hκ' ha₀
    calc (max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)))⁻¹ ≤ (2 / (‖κ‖ * A))⁻¹ :=
          inv_anti₀ (by positivity) (le_max_right _ _)
      _ = ‖κ‖ * (A / 2) := by field_simp
      _ ≤ ‖κ‖ * ‖rw‖ := mul_le_mul_of_nonneg_left hlo hκ'.le
  · calc ‖κ‖ * ‖rw‖ ≤ ‖κ‖ * (3 / 2 * A) := mul_le_mul_of_nonneg_left hhi hκ'.le
      _ = 3 / 2 * (‖κ‖ * A) := by ring
      _ ≤ _ := le_max_left _ _

theorem theta_const_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨κ, r, w₀, w₁, hκ, hr0, h₀, h₁, T', hT'⟩ := exists_chart_theta_unit E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨T₃, C, hC, hb⟩ := exists_bounds_of_sumsAt κ hκ r hr0
  refine ⟨max T' (max Ha.T T₃), C, hC, fun w hw yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨rw, hrw, hval⟩ := hT' w hw.1
  obtain rfl := GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM w hw.2.1 w₀ w₁ h₀ h₁ (κ * rw) hval yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn
  exact hb w hw.2.2 rw hrw

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_lattice_torsion_count : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  intro Q _ g r N e b T hN he _hs hb hT hcard
  haveI : NeZero N := ⟨hN.ne'⟩
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)
  have esub : ∀ v w, e (v - w) = e v * (e w)⁻¹ := by
    intro v w
    have h := he (v - w) w
    rw [sub_add_cancel] at h
    exact eq_mul_inv_of_mul_eq h.symm
  have ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n := by
    intro n v
    induction n with
    | zero => simp [e0]
    | succ n ih => rw [succ_nsmul, he, ih, pow_succ]
  set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ
  have hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j
      = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j := by
    intro a a'
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp [sub_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j := by
    intro c m h
    have h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j := by
      rw [← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    have h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]
      rw [h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]
    have h4 := Fintype.linearIndependent_iff.1 hb.1 _ h3
    intro j
    have := h4 j
    rw [sub_eq_zero] at this
    exact_mod_cast this
  have key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j := by
    intro a a'
    constructor
    · intro h
      have h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1 := by
        rw [← hdiff, esub]
        exact mul_inv_eq_one.2 h
      obtain ⟨m, hm⟩ := (hb.2 _).1 h1
      have := hdvd (fun j => a j - a' j) m hm
      intro j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩
    · intro h
      have hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k := fun j =>
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith
      choose k hk using hk
      have h1 : e (∑ j, k j • b j) = 1 := (hb.2 _).2 ⟨k, rfl⟩
      have h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j := by
        simp_rw [hk, mul_smul, ← Finset.smul_sum]
        rw [Nat.cast_smul_eq_nsmul ℤ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      have h3 := hdiff a a'
      rw [h2] at h3
      have h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j := by
        rw [← h3]; abel
      simp only [hψ, h4, he, h1, _root_.mul_one]
  have hpow : ∀ a, ψ a ^ N = 1 := by
    intro a
    show e _ ^ N = 1
    rw [← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (hb.2 _).2 ⟨a, rfl⟩
  have hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := _hs p
    have h1 : e (N • u) = 1 := by rw [ensmul, hp]
    obtain ⟨m, hm⟩ := (hb.2 _).1 h1
    refine ⟨m, ?_⟩
    show e _ = e u
    rw [← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let F : (Fin r → ZMod N) → Q := fun s => ψ (fun j => ((s j).val : ℤ))
  have hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a := by
    intro a
    exact (key _ _).2 fun j => by simp
  have hFinj : Function.Injective F := by
    intro s s' h
    funext j
    have h1 := (key _ _).1 h j
    simpa using h1
  have hR : Nat.card {p : Q // p ^ N = 1} = N ^ r := by
    have hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1})) := by
      refine ⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩
      obtain ⟨a, ha⟩ := hsurj p.1 p.2
      exact ⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  refine ⟨{s | F s ∈ T}, ?_, ?_⟩
  · have hS : Nat.card {s | F s ∈ T} = Nat.card T := by
      have hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T)) := by
        refine ⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩
        obtain ⟨a, ha⟩ := hsurj τ.1 (hT _ τ.2)
        refine ⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩
        · show F _ ∈ T
          rw [hFval, ha]
          exact τ.2
        · show F _ = _
          rw [hFval, ha]
      exact Nat.card_eq_of_bijective _ hbij
    rw [hS, ← hR, hcard]
  · intro a ha
    show ψ a ∈ T
    rw [← hFval]
    exact ha

end GlobalTheory.ShFam.Hor.LogCh
end

