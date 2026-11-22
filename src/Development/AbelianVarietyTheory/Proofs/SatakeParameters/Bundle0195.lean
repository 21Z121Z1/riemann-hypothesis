import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKillTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.AugmentationEigenvector

section General

variable {K X Y : Type} [Group K] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

def aug (ψ : K →* ℂˣ) : MonoidAlgebra ℂ K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ K ((Units.coeHom ℂ).comp ψ)

theorem aug_single (ψ : K →* ℂˣ) (g : K) (r : ℂ) :
    aug ψ (MonoidAlgebra.single g r) = r * (ψ g : ℂ) := by
  simp [aug]

theorem act_eigen (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (y : X)
    (hy : ∀ g, σ g y = (ψ g : ℂ) • y) (c : MonoidAlgebra ℂ K) :
    σ.asAlgebraHom c y = aug ψ c • y := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]
  | single g r => rw [aug_single, Representation.asAlgebraHom_single, LinearMap.smul_apply, hy, smul_smul]

theorem act_comm (σ : Representation ℂ K X) (τ : Representation ℂ K Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ g x, f (σ g x) = τ g (f x)) (c : MonoidAlgebra ℂ K) (x : X) :
    f (σ.asAlgebraHom c x) = τ.asAlgebraHom c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g r => simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hf]

theorem exists_kill [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (hσ : IsSmooth σ) (hψ : IsSmoothChar ψ)
    (h0 : ∀ z, (∀ g, σ g z = (ψ g : ℂ) • z) → z = 0) (z : X) :
    ∃ c, aug ψ c ≠ 0 ∧ σ.asAlgebraHom c z = 0 := by
  classical
  let π := twist σ ψ⁻¹
  have hπ : IsSmooth π := isSmooth_twist hσ hψ.inv
  have hlc : IsLocallyConstant fun g : K => π g z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h : {g : K | π g z = z} ∈ nhds ((fun y => x⁻¹ * y) x) :=
      IsOpen.mem_nhds (hπ z) (by simp)
    filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
    have hy' : π (x⁻¹ * y) z = z := hy
    calc π y z = π x (π (x⁻¹ * y) z) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = π x z := by rw [hy']
  have hfin := hlc.range_finite
  let O : Finset X := hfin.toFinset
  have hO : ∀ w, w ∈ O ↔ ∃ g, π g z = w := fun w => by simp [O]
  have hmem : ∀ g, ∀ w ∈ O, π g w ∈ O := fun g w hw => by
    obtain ⟨x, rfl⟩ := (hO w).1 hw
    exact (hO _).2 ⟨g * x, by rw [map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ g, π g (∑ w ∈ O, w) = ∑ w ∈ O, w := fun g => by
    rw [map_sum]
    refine Finset.sum_nbij' (fun w => π g w) (fun w => π g⁻¹ w) (hmem g) (hmem g⁻¹)
      (fun w _ => ?_) (fun w _ => ?_) (fun _ _ => rfl)
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hz : ∑ w ∈ O, w = 0 := h0 _ fun g => by
    have h1 := hinv g
    have h2 : π g (∑ w ∈ O, w) = ((ψ g)⁻¹ : ℂˣ).val • σ g (∑ w ∈ O, w) := rfl
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, Units.mul_inv, one_smul]
  choose s hs using fun w : O => (hO w).1 w.2
  refine ⟨∑ w : O, MonoidAlgebra.single (s w) ((ψ (s w))⁻¹ : ℂˣ).val, ?_, ?_⟩
  · rw [map_sum]
    simp only [aug_single, Units.inv_mul]
    have : O.Nonempty := ⟨z, (hO z).2 ⟨1, by simp⟩⟩
    simpa using this.ne_empty
  · rw [map_sum, LinearMap.sum_apply, ← hz, ← Finset.sum_coe_sort O]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact hs w

end General

section Tensor

variable {β : Type} [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (Γ j) (X j)) (a : β) {K : Type} [Group K]
  (i : K →* Γ a)

def viaFactor : Representation ℂ K (⨂[ℂ] j, X j) :=
  (piTensor ρ).comp ((MonoidHom.mulSingle Γ a).comp i)

theorem viaFactor_tprod (x : ∀ j, X j) (g : K) (z : X a) :
    viaFactor ρ a i g (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a (i g) z)) := by
  show piTensor ρ (Pi.mulSingle a (i g)) _ = _
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

theorem viaFactor_alg (x : ∀ j, X j) (c : MonoidAlgebra ℂ K) (z : X a) :
    (viaFactor ρ a i).asAlgebraHom c (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ
        (Function.update x a (Representation.asAlgebraHom ((ρ a).comp i) c z)) :=
  (act_comm ((ρ a).comp i) (viaFactor ρ a i) ((PiTensorProduct.tprod ℂ).toLinearMap x a)
    (fun g z => (viaFactor_tprod ρ a i x g z).symm) c z).symm

theorem exists_kill_tensor (ψ : K →* ℂˣ)
    (h : ∀ z, ∃ c, aug ψ c ≠ 0 ∧ Representation.asAlgebraHom ((ρ a).comp i) c z = 0)
    (v : ⨂[ℂ] j, X j) (b : MonoidAlgebra ℂ K) :
    ∃ c, aug ψ c ≠ 0 ∧
      (viaFactor ρ a i).asAlgebraHom c ((viaFactor ρ a i).asAlgebraHom b v) = 0 := by
  induction v using PiTensorProduct.induction_on generalizing b with
  | smul_tprod r x =>
    obtain ⟨c, hc, hc'⟩ := h (Representation.asAlgebraHom ((ρ a).comp i) b (x a))
    refine ⟨c, hc, ?_⟩
    rw [← Function.update_eq_self a x, map_smul, map_smul, viaFactor_alg, viaFactor_alg, hc',
      MultilinearMap.map_update_zero, smul_zero]
  | add v w hv hw =>
    obtain ⟨c, hc, hc'⟩ := hv b
    obtain ⟨d, hd, hd'⟩ := hw (c * b)
    refine ⟨d * c, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [map_mul, Module.End.mul_apply] at hd'
    rw [map_mul, Module.End.mul_apply, map_add, map_add, hc', zero_add, hd']

end Tensor

theorem exists_eigenvector (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type)
    [(j : β) → Fintype (m j)] [(j : β) → DecidableEq (m j)] (X : β → Type)
    [(j : β) → AddCommGroup (X j)] [(j : β) → Module ℂ (X j)]
    (ρ : (j : β) → Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y)
    (hρ : ∀ j, IsSmooth (ρ j)) (hχ : IsSmoothChar χ) (hs : IsSubquotient τ (piTensor ρ))
    (hy : y ≠ 0)
    (he : ∀ g ∈ KO k (m a),
      τ (Pi.mulSingle a g) y = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • y) :
    ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a),
      ρ a g z = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • z := by
  by_contra hne
  haveI : CompactSpace (KO k (m a)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  let i := (KO k (m a)).subtype
  let ψ : KO k (m a) →* ℂˣ := χ.comp (Matrix.GeneralLinearGroup.det.comp i)
  have hψ : IsSmoothChar ψ :=
    hχ.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  have h1 := exists_kill ((ρ a).comp i) ψ (isSmooth_comp (hρ a) i continuous_subtype_val) hψ
    fun z hz => by
      by_contra h
      exact hne ⟨z, h, fun g hg => hz ⟨g, hg⟩⟩
  obtain ⟨S, f, hf⟩ := hs
  obtain ⟨v, rfl⟩ := hf y
  obtain ⟨c, hc, hc'⟩ := exists_kill_tensor ρ a i ψ h1 v.1 1
  rw [map_one, Module.End.one_apply] at hc'
  let e : KO k (m a) →* Levi k m := (MonoidHom.mulSingle (fun j => GL (m j) k) a).comp i
  have h2 := act_comm (S.toRepresentation.comp e) (viaFactor ρ a i) S.toSubmodule.subtype
    (fun _ _ => rfl) c v
  have h3 : Representation.asAlgebraHom (S.toRepresentation.comp e) c v = 0 :=
    Subtype.ext (h2.trans hc')
  have h4 := act_comm (S.toRepresentation.comp e) (τ.comp e) f.toLinearMap
    (fun g x => f.isIntertwining _ _ (e g) x) c v
  rw [h3, map_zero, act_eigen (τ.comp e) ψ (f.toLinearMap v) (fun g => he g.1 g.2)] at h4
  exact hy ((smul_eq_zero.1 h4.symm).resolve_left hc)

end GlobalTheory.AugmentationEigenvector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
namespace GlobalTheory.Cong.LevelExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_locU_iff {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) :
    x ∈ locU n w ↔ x ∈ finU E n ∧ ∀ u, Apart u w → cLoc u x = 1 := by
  unfold locU Apart
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem cLoc_conj_eq_one {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) (h1 : cLoc w x = 1) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.one_mul] at hce
  exact Units.ext hce

theorem one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (x : UA E n) (h1 : cLoc w x = 1) :
    ∀ u, ¬ Apart u w → cLoc u x = 1 := by
  intro u hu
  have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    by_contra h
    exact hu h
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu' with rfl | rfl
  · exact h1
  · exact cLoc_conj_eq_one x h1

end GlobalTheory.Cong.LevelExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponents
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocSplitGraph

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  intro L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE
  obtain ⟨E⟩ := hE
  obtain ⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩ := h₁
  obtain ⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩ := h₂

  have hci : i₁ = i₂ := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂ := by
      refine hd.equalizer hi₁ hi₂ (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hiL₁, hiL₂]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  let F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W) := T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)
  have hF : ∀ u, F u = (T₁ u, T₂ (E u)) := fun u => rfl
  have hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u) := fun g u => LinearMap.congr_fun (E.isIntertwining' g) u
  have hnt : Nontrivial σ₁.V := by
    haveI := σ₁.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ₁.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  refine ⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : σ₁.V)
    intro h
    have hm : F u ∈ LinearMap.range F := ⟨u, rfl⟩
    rw [h, Submodule.mem_bot, hF, Prod.mk_eq_zero] at hm
    exact hu (hT₁inj (hm.1.trans (map_zero T₁).symm))
  · rintro _ ⟨u, rfl⟩
    exact ⟨hT₁S u, hT₂S (E u)⟩
  · rintro x hx _ ⟨u, rfl⟩
    refine ⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩
    rw [hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : v = 0 := hT₁inj (hv.1.trans (map_zero T₁).symm)
    rw [← hv.2, hv0, map_zero, map_zero]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : E v = 0 := hT₂inj (hv.2.trans (map_zero T₂).symm)
    have : v = 0 := by simpa using hv0
    rw [← hv.1, this, map_zero]

end GlobalTheory.LocSplitGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familySplitOperators_eq_labelOperators_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  first | exact @GlobalTheory.SplitHeckeLabel.split_ops | exact GlobalTheory.SplitHeckeLabel.split_ops | (intros; apply GlobalTheory.SplitHeckeLabel.split_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ t P, Good R t P → (∀ k, k + 1 < D.R.m → ∀ φ, IsVacAt R.ψ _ _ P (R.ptY t k φ)) ∧ (∀ φ, IsVacAt R.ψ _ _ P (R.ptX t φ)) ∧ ∀ i φ, IsVacAt R.ψ _ _ P (R.ptP i t φ) := by
  first | exact @GlobalTheory.VacGood.fock_vacua_good | exact GlobalTheory.VacGood.fock_vacua_good | (intros; apply GlobalTheory.VacGood.fock_vacua_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinates
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord.FrobMove

theorem inv_map_field {E K : Type*} [Field E] [Field K] (f : E →+* K) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) : (M.map f)⁻¹ = M⁻¹.map f := by
  have hd : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  have ha : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm
  rw [Matrix.inv_def, Matrix.inv_def, hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem frob_moves_coords : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b
  choose ρ hρ using exists_ringHom_rhoK D lam σ hσ hcl
  have hfun : ∀ z, rhoK D lam z = ⇑(ρ z) := fun z => funext fun y => (hρ z y).1
  have hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y) := fun z y => by
    rw [← (hρ z y).1, ← (hρ _ _).1]; exact sigma_rhoK D lam σ hσ hcl z y
  have hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E),
      (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1)) := fun z Q => by
    ext i j; simp [hs]
  have hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j,
      σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j := fun z Q i j => by
    rw [← hsm, inv_map_field σ]; rfl
  have K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = 1 := by
    intro n Q hQ z
    have e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map
          (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1)) := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp [conj_conj]
    rw [e, hQ z]
    simp
  have K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ =
        ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose := fun Q hQ z =>
    Matrix.inv_eq_left_inv (K Q hQ z)
  have K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹).transpose := fun Q hQ z => by
    rw [Matrix.transpose_nonsing_inv]; exact (Matrix.inv_eq_right_inv (K Q hQ z)).symm
  have hPc := hP.2.1 hcl
  have hP'c := hP'.2.1 hcl
  refine ⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩
  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, conj_conj, hinv, K1 P hPc z]
    have e2 := congrFun (congrFun (K2 P' hP'c z) b₁) b₀
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring
  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, hinv, K1 P' hP'c w]
    have e2 := congrFun (congrFun (K2 P hPc w) a₁) a
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring

end GlobalTheory.KerStd.HypCoord.FrobMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeComp

theorem smooth_loc {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  have hu := unif_spec w
  set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc
  have hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1)) := by
    unfold IsUnifAt at hu
    rw [hc, map_pow, hu, ← WithZero.exp_nsmul]; congr 1; simp
  have ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E} :=
    (Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1 := hx
  rw [map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul] at h1
  have h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  refine hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))
  have := Valuation.map_one_add_of_lt _ h2
  rwa [add_sub_cancel] at this

theorem eq_of_isComp {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {ξ ξ' : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : IsComp χ w ξ) (hξ' : IsComp χ w ξ') : ξ' = ξ := by
  have hs := hξ'.1.mul hξ.1.inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ' _ * (ξ _)⁻¹ = 1
  rw [hξ.2, hξ'.2]
  exact mul_inv_cancel _

theorem main : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  intro E _ _ χ w
  have hc : IsComp χ w (χ.loc w) := ⟨smooth_loc χ w, fun _ => rfl⟩
  exact ⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩

end GlobalTheory.HeckeComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisBis
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PartOrthPin

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) → GlobalTheory.ThetaExh.PartOrth D.nd i := by
  intro hL D P i ⟨X⟩ σ σ' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hni : ¬ (P.rep σ).Iso (P.rep σ') := fun h => hne (P.rep_inj σ σ' h)
  rw [X.φ_inner]
  exact GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos X.stab X.inv X.adm
    (P.rep σ) (P.rep σ') hni _ ((X.isot σ u).1 hu) _ ((X.isot σ' v).1 hv)

end GlobalTheory.PartOrthPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPointStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)), IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  first | exact @GlobalTheory.isOfFinOrder_of_conj_mem_ratU | exact GlobalTheory.isOfFinOrder_of_conj_mem_ratU | (intros; apply GlobalTheory.isOfFinOrder_of_conj_mem_ratU; all_goals assumption)
end

