import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousGrpHom
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.CompactDualSwap

variable {P Q P' Q' : ℕ}

def AntiIso (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') : Prop :=
  (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = -Formalism.UG.Jpq P' Q'

theorem AntiIso.symm {e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q'} (h : AntiIso e) : AntiIso e.symm := by
  unfold AntiIso at *
  ext i j
  have := congrFun (congrFun h (e i)) (e j)
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.neg_apply, Equiv.symm_symm] at *
  rw [this, neg_neg]

def grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q →* UpqT P' Q' :=
  let f : Formalism.UG.Upq P Q →* GL (Fin P' ⊕ Fin Q') ℂ :=
    (Units.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom).comp (Formalism.UG.Upq P Q).subtype
  let f' : Formalism.UG.Upq P Q →* Formalism.UG.Upq P' Q' := f.codRestrict _ (by
    rintro ⟨g, hg⟩
    change Formalism.UG.cT _ g.val * _ * g.val = _ at hg
    change Formalism.UG.cT _ (g.val.submatrix e.symm e.symm) * _ *
      (g.val.submatrix e.symm e.symm) = _
    have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
      rw [h, neg_neg]
    have h3 : Formalism.UG.cT (starRingEnd ℂ) (g.val.submatrix e.symm e.symm) =
      (Formalism.UG.cT (starRingEnd ℂ) g.val).submatrix e.symm e.symm := rfl
    rw [h2, h3, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hg])
  f'

theorem mat_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (g : UpqT P Q) :
    (grpHom e h g).mat = g.mat.submatrix e.symm e.symm := rfl

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → _) :=
  (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective

theorem continuous_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) :
    Continuous (grpHom e h) := by
  rw [(GlobalTheory.UpqTopology.upq_lcsc P' Q').2.2.2.2.2.isInducing.continuous_iff]
  exact ((GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.continuous).matrix_submatrix e.symm e.symm

def grpEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q ≃ₜ* UpqT P' Q' where
  toFun := grpHom e h
  invFun := grpHom e.symm h.symm
  left_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  right_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  map_mul' := map_mul _
  continuous_toFun := continuous_grpHom e h
  continuous_invFun := continuous_grpHom e.symm h.symm

theorem lie_mem (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    X.val.submatrix e.symm e.symm ∈ lieU P' Q' := by
  have hX : X.valᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.val = 0 := X.2
  change (X.val.submatrix e.symm e.symm)ᴴ * Formalism.UG.Jpq P' Q' +
    Formalism.UG.Jpq P' Q' * X.val.submatrix e.symm e.symm = 0
  have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
    rw [h, neg_neg]
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← neg_add, neg_eq_zero]
  have := congrArg (fun M => Matrix.submatrix M e.symm e.symm) hX
  exact this

def lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : lieU P Q ≃L[ℝ] lieU P' Q' where
  toFun X := ⟨_, lie_mem e h X⟩
  invFun X := ⟨_, lie_mem e.symm h.symm X⟩
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := rfl
  map_smul' c X := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix e.symm e.symm).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix e e).subtype_mk _

theorem coe_lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    ((lieEquiv e h X : lieU P' Q') : Matrix _ _ ℂ) = X.val.submatrix e.symm e.symm := rfl

theorem mem_ball (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) (r : ℝ) :
    lieEquiv e h X ∈ ballU P' Q' r ↔ X ∈ ballU P Q r := by
  simp only [ballU, Set.mem_ofPred_eq, coe_lieEquiv, submatrix_apply]
  have : ∑ i, ∑ j, ‖X.val (e.symm i) (e.symm j)‖ = ∑ i, ∑ j, ‖X.val i j‖ := by
    rw [← e.symm.sum_comp (fun i => ∑ j, ‖X.val i j‖)]
    exact Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X.val (e.symm i) j‖)
  rw [this]

open scoped Matrix.Norms.Operator in
theorem exp_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (X.submatrix e.symm e.symm) = (NormedSpace.exp X).submatrix e.symm e.symm :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (continuous_id.matrix_submatrix e.symm e.symm) X).symm

theorem isOmegaLeb_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (lam : Measure (lieU P Q)) (hl : IsOmegaLeb lam) : IsOmegaLeb (lam.map (lieEquiv e h)) := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl
  refine ⟨(lieEquiv e h).isAddHaarMeasure_map lam, ?_⟩
  have hm : Measurable (lieEquiv e h) := (lieEquiv e h).continuous.measurable
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hv := volume_measurePreserving_piCongrLeft
    (fun _ : (Fin P' ⊕ Fin Q') × (Fin P' ⊕ Fin Q') => ℂ) (e.prodCongr e)
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P' Q').measurable (hm.prodMap hm),
    ← hv.map_eq, ← h2, Measure.map_map hv.measurable (hc P Q).measurable]
  congr 1
  funext ab ij
  obtain ⟨ij, rfl⟩ := (e.prodCongr e).surjective ij
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  simp [entries, coe_lieEquiv]

theorem omegaDensity_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (μ : Measure (UpqT P Q)) (c : ENNReal) (hμ : OmegaDensity μ c) :
    OmegaDensity (μ.map (grpEquiv e h)) c := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : BorelSpace (UpqT P' Q') := ⟨rfl⟩
  obtain ⟨lam, hl, ht⟩ := hμ
  refine ⟨_, isOmegaLeb_map e h lam hl, ?_⟩
  refine ht.congr fun r => ?_
  have e1 := (grpEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := μ)
  have e2 := (lieEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := lam)
  congr 1
  · refine Eq.trans ?_ (e1 _).symm
    congr 1
    ext g
    change (∃ X ∈ ballU P Q r, _) ↔ ∃ X ∈ ballU P' Q' r, g.mat.submatrix e.symm e.symm = _
    rw [(lieEquiv e h).surjective.exists]
    refine exists_congr fun X => ?_
    rw [mem_ball, coe_lieEquiv, exp_submatrix]
    refine and_congr_right fun _ => ⟨fun hh => by rw [hh], fun hh => ?_⟩
    ext i j
    simpa using congrFun (congrFun hh (e i)) (e j)
  · refine Eq.trans ?_ (e2 _).symm
    congr 1
    ext X
    exact (mem_ball e h X r).symm

def swapIdx (N : ℕ) : Fin 0 ⊕ Fin N ≃ Fin (0 + N) ⊕ Fin 0 :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (finCongr (Nat.zero_add N).symm) (Equiv.refl _))

theorem antiIso_swapIdx (N : ℕ) : AntiIso (swapIdx N) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [swapIdx, Formalism.UG.Jpq, Matrix.one_apply, Fin.ext_iff]
    · exact j.elim0
  · exact i.elim0

theorem cd_zero_univ : ∀ (c : CDHaar) (N : ℕ), c.cd 0 N Set.univ = 1 := by
  intro c N
  obtain ⟨d, hd0, hdt, h1, h2⟩ := c.trick 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (0 + N) 0
  have := c.haar 0 N
  have := c.haar (0 + N) 0
  have := c.prob (0 + N)
  let G := grpEquiv (swapIdx N) (antiIso_swapIdx N)
  have : ((c.cd 0 N).map G).IsHaarMeasure := G.isHaarMeasure_map _
  have h3 := omegaDensity_map _ (antiIso_swapIdx N) _ _ h1
  have h4 := Measure.isMulLeftInvariant_eq_smul ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  set a := Measure.haarScalarFactor ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  have h5 : OmegaDensity ((c.cd 0 N).map G) (a * d) := by
    rw [h4]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h2).2 a
  have h6 : (a : ENNReal) * d = 1 * d := by
    rw [one_mul]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h3).1 _ h5
  have h7 : (a : ENNReal) = 1 := (ENNReal.mul_left_inj hd0 hdt).1 h6
  have h8 : ((c.cd 0 N).map G) Set.univ = 1 := by
    rw [h4, Measure.smul_apply, measure_univ, ENNReal.smul_def, h7, one_smul]
  have hG : Measurable G := G.continuous.measurable
  rwa [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h8

end GlobalTheory.CompactDualSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSections
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

theorem Proportional.basicOpen_le_chart {R : Type} [CommRing R] {X W : Scheme.{0}} {L : LB X} {m : ℕ}
    {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) :
    W.basicOpen ((g.appLE (L.U k) A hk).hom ((σ i).f k)) ≤ ψ ⁻¹ᵁ chart R m i := by
  intro z hz
  obtain ⟨i', hi'⟩ := (isCoordFamily_pullRatio ψ).exists_mem z
  have hA : z ∈ A := W.basicOpen_le _ hz
  have e := h (A ⊓ ψ ⁻¹ᵁ chart R m i') k (inf_le_left.trans hk) i' inf_le_right i
  have e' := congrArg W.basicOpen e
  rw [Scheme.basicOpen_mul, basicOpen_pullRatio, Scheme.basicOpen_appLE] at e'
  rw [Scheme.basicOpen_appLE] at hz
  have hz' : z ∈ (A ⊓ ψ ⁻¹ᵁ chart R m i') ⊓ g ⁻¹ᵁ X.basicOpen ((σ i).f k) := ⟨⟨hA, hi'⟩, hz.2⟩
  exact (e'.le hz').1.2

theorem eq_of_proportional :
    ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  intro R _ X W L m σ g ψ ψ' hG hs h h'
  refine hom_ext hs fun y => ?_
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hG.1.ge (Set.mem_univ y))
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAk⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hk (g ⁻¹ᵁ L.U k).isOpen
  have hAk' : A ≤ g ⁻¹ᵁ L.U k := hAk
  have hsp := hG.2 k ⟨A, hA⟩ hAk'
  have hsp' : Ideal.span (Set.range fun j => (g.appLE (L.U k) A hAk').hom ((σ j).f k)) = ⊤ := hsp.symm
  have hcov := (IsAffineOpen.self_le_iSup_basicOpen_iff hA).2 hsp'
  obtain ⟨⟨_, i, rfl⟩, hi⟩ := Opens.mem_iSup.1 (hcov hyA)
  have hB := W.basicOpen_le ((g.appLE (L.U k) A hAk').hom ((σ i).f k))
  refine ⟨_, hi, i, h.basicOpen_le_chart A k hAk' i, h'.basicOpen_le_chart A k hAk' i, fun j => ?_⟩
  have hu : IsUnit ((g.appLE (L.U k) _ (hB.trans hAk')).hom ((σ i).f k)) := by
    rw [← resG_appLE g hAk' hB]
    exact RingedSpace.isUnit_res_basicOpen _ _
  exact hu.mul_right_cancel ((h _ k _ i _ j).symm.trans (h' _ k _ i _ j))

end GlobalTheory.ProjBlowup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedSubschemeOpenPieces
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedUnion

theorem isOpenImmersion_of_isImmersion_of_isOpen_range {X Y : Scheme.{0}} (e : X ⟶ Y)
    [IsImmersion e] [IsReduced Y] (h : IsOpen (Set.range e)) : IsOpenImmersion e := by
  let V : Y.Opens := ⟨Set.range e, h⟩
  have hV : Set.range e ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let j : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι e hV
  have hj : j ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hs : Function.Surjective j := fun y => by
    obtain ⟨c, hc⟩ : V.ι y ∈ Set.range e := y.2
    refine ⟨c, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← hc, ← hj]
    rfl
  have : Surjective j := ⟨hs⟩
  have : IsImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  have : IsImmersion j := IsImmersion.of_comp j V.ι
  have : IsClosedImmersion j :=
    .of_isPreimmersion _ (by rw [hs.range_eq]; exact isClosed_univ)
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  rw [← hj]
  infer_instance

theorem exists_closed_union : ∀ (P : Scheme.{0}) (J : Type) [Finite J] (T : J → Scheme.{0}) (i : ∀ k, T k ⟶ P) (Ω : P.Opens), (∀ k, IsImmersion (i k)) → (∀ k, IsReduced (T k)) → (∀ k, ∃ U : P.Opens, Set.range (i k) = (⋃ k', Set.range (i k')) ∩ (U : Set P)) → (∃ F : Set P, IsClosed F ∧ ⋃ k, Set.range (i k) = F ∩ (Ω : Set P)) → ∃ (U : Scheme.{0}) (j : U ⟶ Ω.toScheme) (e : ∀ k, T k ⟶ U), IsClosedImmersion j ∧ (∀ k, IsOpenImmersion (e k)) ∧ (∀ k, e k ≫ j ≫ Ω.ι = i k) ∧ ⋃ k, Set.range (e k) = Set.univ := by
  intro P J _ T i Ω himm hred hU ⟨F, hF, hFΩ⟩
  have hsub : ∀ k c, i k c ∈ F ∩ (Ω : Set P) := fun k c => by
    rw [← hFΩ]
    exact Set.mem_iUnion.mpr ⟨k, c, rfl⟩
  have hiΩ : ∀ k, Set.range (i k) ⊆ Set.range Ω.ι := fun k => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hsub k c).2
  let l : ∀ k, T k ⟶ Ω.toScheme := fun k => IsOpenImmersion.lift Ω.ι (i k) (hiΩ k)
  have hl : ∀ k, l k ≫ Ω.ι = i k := fun k => IsOpenImmersion.lift_fac _ _ _
  let Z : TopologicalSpace.Closeds Ω.toScheme := ⟨Ω.ι ⁻¹' F, hF.preimage Ω.ι.continuous⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ Ω.toScheme := I.subschemeι
  have hg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hlZ : ∀ k, Set.range (l k) ⊆ Z := fun k => by
    rintro _ ⟨c, rfl⟩
    change Ω.ι (l k c) ∈ F
    have : Ω.ι (l k c) = i k c := by rw [← hl k]; rfl
    rw [this]
    exact (hsub k c).1
  have hker : ∀ k, g.ker ≤ (l k).ker := fun k => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (l k) Z (hlZ k)
  let e : ∀ k, T k ⟶ I.subscheme := fun k => IsClosedImmersion.lift g (l k) (hker k)
  have heg : ∀ k, e k ≫ g = l k := fun k => IsClosedImmersion.lift_fac _ _ _
  have hei : ∀ k, e k ≫ g ≫ Ω.ι = i k := fun k => by
    rw [← hl k, ← heg k, Category.assoc]
  have hpt : ∀ k c, (g ≫ Ω.ι) (e k c) = i k c := fun k c => by rw [← hei k]; rfl
  have hinj : Function.Injective (g ≫ Ω.ι) := (g ≫ Ω.ι).isEmbedding.injective
  have hall : ∀ x, (g ≫ Ω.ι) x ∈ ⋃ k, Set.range (i k) := fun x => by
    rw [hFΩ]
    have h1 : g x ∈ (Z : Set Ω.toScheme) := hg ▸ ⟨x, rfl⟩
    exact ⟨h1, (g x).2⟩
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, g, e, inferInstance, fun k => ?_, hei, ?_⟩
  · have : IsImmersion (e k ≫ g ≫ Ω.ι) := by rw [hei]; infer_instance
    have : IsImmersion (e k) := IsImmersion.of_comp _ (g ≫ Ω.ι)
    obtain ⟨W, hW⟩ := hU k
    refine isOpenImmersion_of_isImmersion_of_isOpen_range _ ?_
    have : Set.range (e k) = (g ≫ Ω.ι) ⁻¹' (W : Set P) := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        have : i k c ∈ Set.range (i k) := ⟨c, rfl⟩
        rw [hW, ← hpt] at this
        exact this.2
      · intro hx
        have : (g ≫ Ω.ι) x ∈ Set.range (i k) := by
          rw [hW]
          exact ⟨hall x, hx⟩
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hinj ((hpt k c).trans hc)⟩
    rw [this]
    exact W.isOpen.preimage (g ≫ Ω.ι).continuous
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨k, c, hc⟩ := Set.mem_iUnion.mp (hall x)
    exact Set.mem_iUnion.mpr ⟨k, c, hinj ((hpt k c).trans hc)⟩

end GlobalTheory.ReducedUnion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLatticesStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), GlobalTheory.BetaEx.Bdd (M' ⊔ M) → (∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ GlobalTheory.BetaEx.detSpan (M ⊓ M') = 𝔞 • GlobalTheory.BetaEx.detSpan M ∧ GlobalTheory.BetaEx.detSpan M' = 𝔞 • GlobalTheory.BetaEx.detSpan (M' ⊔ M) ∧ Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  first | exact @GlobalTheory.BetaEx.exists_index_ideal_inf_sup | exact GlobalTheory.BetaEx.exists_index_ideal_inf_sup | (intros; apply GlobalTheory.BetaEx.exists_index_ideal_inf_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_lattice_eq_lamOf : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  first | exact @GlobalTheory.Mem.Col2.exists_curve_lattice | exact GlobalTheory.Mem.Col2.exists_curve_lattice | (intros; apply GlobalTheory.Mem.Col2.exists_curve_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOfStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finExt_conj_entries_mem_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  first | exact @GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | exact GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | (intros; apply GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem GlobalTheory.TameRecip.exists_ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro H E Ω _ _ _ _ _ _ art ha v A hA ϖ hϖ1 hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := by
    unfold normV
    have : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    exact Finite.one_lt_card
  have hn : 0 < normV v - 1 := by omega
  have hvE : ∀ a : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = v.valuation E (a : E) :=
    fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hu1 : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [hvE]
    refine le_antisymm (v.valuation_le_one u) (not_lt.mp fun h => ?_)
    have hm : u ∈ v.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mp h
    have hlt : Valued.v (x : v.adicCompletion E) < 1 := by
      have e : (x : v.adicCompletion E) = ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) +
          algebraMap E (v.adicCompletion E) (u : E) := by ring
      rw [e]
      refine Valuation.map_add_lt _ hxu ?_
      rw [hvE]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rw [hx'] at hlt
    exact lt_irrefl _ hlt
  have hu : u ∉ v.asIdeal := by
    intro hm
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    rw [← hvE, hu1] at h
    exact lt_irrefl _ h
  have hu0 : algebraMap E (v.adicCompletion E) (u : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  let uc : (v.adicCompletion E)ˣ := Units.mk0 _ hu0
  have hy : Valued.v (((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have e : ((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) *
          (algebraMap E (v.adicCompletion E) (u : E))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uc, Units.val_mk0]
      field_simp
    rw [e, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hxu
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (x * uc⁻¹) hy
  obtain ⟨ρ, hρ, hρz⟩ := (ha.ine v A hA _).mp ⟨z, hz1, rfl⟩
  obtain ⟨τ, hτF, hτπ, hτc⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA ϖ hϖ1 hϖ2 π hπ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) hn
  have h1' : u * ϖ ∈ v.asIdeal := Ideal.mul_mem_left _ _ hϖ1
  have h2' : u * ϖ ∉ v.asIdeal ^ 2 := by
    intro h
    rcases Ideal.IsPrime.mul_mem_pow v.asIdeal h with h3 | h3
    · exact hu h3
    · exact hϖ2 h3
  have hπ' : (π * t) ^ (normV v - 1) = algebraMap E Ω ((u * ϖ : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    ring_nf
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA (u * ϖ) h1' h2' (π * t) hπ'
  have hσ0 : τ'⁻¹ * τ ∈ Ine (F := E) A := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 hπ
  have hval := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hu π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  have hc0 : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ((map_ne_zero _).mpr hϖ0)
  have huE : (u : E) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hcast : ((u * ϖ : 𝓞 E) : E) = (u : E) * (ϖ : E) := by push_cast; ring
  have hs0 : ((-1) ^ normV v : v.adicCompletion E) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hϖc : algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hc0' : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (((u * ϖ : 𝓞 E)) : E) ≠ 0 := by
    rw [hcast, map_mul]
    exact mul_ne_zero hs0 (mul_ne_zero hu0 hϖc)
  have ec := hτc (Units.mk0 _ hc0) rfl
  have ec' := hτ'c (Units.mk0 _ hc0') rfl
  have hmain : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v uc) := by
    have e1 : toAb E Ω τ = (art (localIdele E v (Units.mk0 _ hc0)))⁻¹ := by
      rw [← ec, map_inv, inv_inv]
    rw [map_mul, ec', e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, uc]
    rw [hcast, map_mul]
    field_simp
  refine ⟨τ'⁻¹ * τ * ρ ^ (normV v - 1), mul_mem hσ0 (pow_mem hρ _), ?_, ?_⟩
  · rw [map_mul, map_pow, hmain, hρz, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hz]
    congr 1
    rw [mul_comm x, mul_inv_cancel_left]
  · have e : (τ'⁻¹ * τ * ρ ^ (normV v - 1)) π = (τ'⁻¹ * τ) π := by
      rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρ]
    rw [e]
    exact hval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
section
open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar

end GlobalTheory.MinfMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationDominatedStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_dominated : ∀ (A B k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → (∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  first | exact @GlobalTheory.exists_normal_localization_chart_centred | exact GlobalTheory.exists_normal_localization_chart_centred | (intros; apply GlobalTheory.exists_normal_localization_chart_centred <;> assumption)
end

