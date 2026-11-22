import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisintegrationDensityExists
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.CuspCutCoef

theorem isCuspFn_cutCoef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro k _ _ _ _ _ _ N V _ _ π hπ v l hl f hf
  have hsm : IsSmooth π := hπ.1
  have hU : {g : GL (Fin N) k | π g v = v} ∩ {g | ∀ y, l (π g y) = l y} ∈ nhds (1 : GL (Fin N) k) :=
    Filter.inter_mem ((hsm v).mem_nhds (by simp)) (GlobalTheory.CuspCoef.fix_mem_nhds π l hl)
  obtain ⟨γ, hγ, hsub⟩ := GlobalTheory.CentralExponent.exists_cong_subset hU
  set K0 := GlobalTheory.CentralExponent.cong (Fin N) γ hγ with hK0
  have hK0val : ∀ x ∈ K0, ValuativeRel.valuation k (x : Matrix (Fin N) (Fin N) k).det = 1 := by
    intro x hx
    have h1 : x ∈ GlobalTheory.SplitWeil.KO k (Fin N) :=
      KOne_le_KO (mem_KOne.2 fun i j => (hx i j).trans_le hγ)
    obtain ⟨y, rfl⟩ := h1
    have h2 : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k).det = algebraMap 𝒪[k] k (y : Matrix (Fin N) (Fin N) 𝒪[k]).det :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h2]
    exact (Valuation.integer.integers (ValuativeRel.valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)
  have hbi : ∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g := by
    intro x hx y hy g
    rw [hf, hf]
    have hd : ValuativeRel.valuation k ((x * g * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
        ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
        hK0val x hx, hK0val y hy, one_mul, mul_one]
    rw [hd]
    split_ifs
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hsub y hy).1, (hsub x hx).2]
    · rfl
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_
    have hc : Continuous fun y : GL (Fin N) k => g⁻¹ * y := continuous_const.mul continuous_id
    have : ∀ᶠ y in nhds g, g⁻¹ * y ∈ K0 :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [inv_mul_cancel]
        exact (GlobalTheory.CentralExponent.isOpen_cong γ hγ).mem_nhds K0.one_mem)
    filter_upwards [this] with y hy
    have := hbi 1 K0.one_mem (g⁻¹ * y) hy g
    rwa [one_mul, mul_inv_cancel_left] at this
  obtain ⟨C, hC, hCs⟩ := (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k N V π hπ).2 v l hl
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.T.central_translate_det_one_compact k N C hC
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro hD fun g hg => ?_
    rw [hf]
    split_ifs with h
    · by_contra h0
      obtain ⟨z, hz, c, hc, rfl⟩ := hCs g h0
      exact hg (hDs z hz c hc h)
    · rfl
  refine ⟨hlc, hcs, K0, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, hbi, ?_⟩
  intro a b e ha hb μ hμ u hu g h
  obtain ⟨huc, hum, hud, hup⟩ := GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport k N a b e u hu
  by_cases hg : ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1
  · refine GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero k N V π hsm a b μ hμ u huc hum (l ∘ₗ π (g * h⁻¹)) (π h v)
      (GlobalTheory.T.cuspidal_unipotent_vanishing k N V π hπ a b e ha hb u hu _) _ (hup f hcs g h) fun X => ?_
    have hd : ValuativeRel.valuation k ((g * (h⁻¹ * u X * h) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, hg, one_mul, mul_one]
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one]
    rw [hf, if_pos hd]
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  · have : (fun X => f (g * (h⁻¹ * u X * h))) = fun _ => 0 := by
      funext X
      rw [hf, if_neg]
      intro hd
      apply hg
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, mul_one] at hd
      rwa [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one, mul_one] at hd
    rw [this, integral_zero]

end GlobalTheory.CuspCutCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivGOfLocalIsometry
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

noncomputable def evVec {n : Type} (v : HeightOneSpectrum (𝓞 F)) (x : n → Af F ⊗[F] E) : n → Fv F v ⊗[F] E :=
  fun i => evF E v (x i)

theorem evVec_mul {n : Type} (v : HeightOneSpectrum (𝓞 F)) (ε : Af F ⊗[F] E) (x : n → Af F ⊗[F] E) :
    evVec v (fun a => ε * x a) = evF E v ε • evVec v x := by
  funext a
  exact map_mul _ _ _

theorem evVec_mulVec {m n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F))
    (A : Matrix m n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    evVec v (A.mulVec z) = (A.map (evF E v)).mulVec (evVec v z) := by
  funext a
  exact RingHom.map_mulVec _ _ _ _

theorem evVec_sgT {n : Type} (v : HeightOneSpectrum (𝓞 F)) (y : n → Fv F v ⊗[F] E) :
    evVec v (fun i => sgT E v (y i)) = y := by
  funext a
  exact evF_sgT_self _ _

theorem mul_eq_iff {n : Type} {v : HeightOneSpectrum (𝓞 F)} {ε : Af F ⊗[F] E}
    (hε : ∀ w, w ≠ v → evF E w ε = 0) (x x' : n → Af F ⊗[F] E) :
    ((fun a => ε * x a) = fun a => ε * x' a) ↔ evF E v ε • evVec v x = evF E v ε • evVec v x' := by
  rw [← evVec_mul, ← evVec_mul]
  refine ⟨fun h => by rw [h], fun h => funext fun a => evF_ext fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact congrFun h a
  · rw [map_mul, map_mul, hε w hw, zero_mul, zero_mul]

theorem evVec_newBasis {m n : ℕ} (hr : m = n) (v : HeightOneSpectrum (𝓞 F))
    (φ : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (B : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (z : Fin m → Af F ⊗[F] E) :
    evVec v (((φ.map (sgT E v) * B).submatrix id (Fin.cast hr)).mulVec z) =
      φ.mulVec (evVec v (B.mulVec fun i => z (Fin.cast hr.symm i))) := by
  subst hr
  have h : (φ.map (sgT E v)).map (evF E v) = φ := by
    ext i j : 1
    exact evF_sgT_self _ _
  show evVec v ((φ.map (sgT E v) * B).mulVec z) = φ.mulVec (evVec v (B.mulVec z))
  rw [← Matrix.mulVec_mulVec, evVec_mulVec, h]

theorem mul_mem_lamHat_iff [NumberField E] [StarRing E] (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}
    {ε : Af F ⊗[F] E} (hε : ∀ w, w ≠ v → evF E w ε = 0) (x : Fin V.rank → Af F ⊗[F] E) :
    (fun a => ε * x a) ∈ lamHat F V ↔ evF E v ε • evVec v x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  rw [mem_lamHat_iff, ← evVec_mul]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · simp only [map_mul, hε w hw, zero_mul]; exact zero_mem _

theorem divG_of_local_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → ∀ (hr : V'.rank = V.rank) (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram) (g' : HA (AF F) hc.sig V'.gram), f * e = e → (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ → DivG hc V e ϖ d g → DivG hc V' e ϖ (fun i => d (Fin.cast hr i)) g' := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf hφψ hψφ hL hr e ϖ d g g' hfe hg ⟨B, h1, h2, h3, h4⟩
  have hε : ∀ w, w ≠ v → evF E w (finP F E e) = 0 := ((GlobalTheory.SuppLocal.idem_mul_iff hf e).1 hfe).2
  have hback : ∀ y, φ.mulVec (ψ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  have hback' : ∀ y, ψ.mulVec (φ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hψφ, Matrix.one_mulVec]
  have hψ : ∀ y ∈ lamHat F V', (fun i => sgT E v (ψ.mulVec (evVec v y) i)) ∈ lamHat F V := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hL _).2 (by rw [hback]; exact (mem_lamHat_iff V' y).1 hy v))
  have hφ : ∀ y ∈ lamHat F V, (fun i => sgT E v (φ.mulVec (evVec v y) i)) ∈ lamHat F V' := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V' v ((hL _).1 ((mem_lamHat_iff V y).1 hy v))
  have hg' : ∀ y, evVec v ((finMat hc.sig V'.gram g').mulVec y) =
      φ.mulVec (((finMat hc.sig V.gram g).map (evF E v)).mulVec (ψ.mulVec (evVec v y))) := fun y => by
    rw [evVec_mulVec, ← locMat_val, hg, locMat_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨(φ.map (sgT E v) * B).submatrix id (Fin.cast hr), fun z hz => ?_, fun y hy => ?_, fun y hy => ?_,
    fun z hz => ?_⟩
  · rw [mul_mem_lamHat_iff V' hε, evVec_newBasis, ← Matrix.mulVec_smul, ← hL, ← mul_mem_lamHat_iff V hε]
    exact h1 _ fun i => hz _
  · obtain ⟨z, hz, e2⟩ := h2 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, ← Matrix.mulVec_smul]
    refine Eq.trans ?_ (congrArg φ.mulVec e2)
    rw [Matrix.mulVec_smul, hback]
  · obtain ⟨z, hz, e2⟩ := h3 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2
  · obtain ⟨y, hy, e2⟩ := h4 (fun i => z (Fin.cast hr.symm i)) fun i => hz _
    refine ⟨_, hφ y hy, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', evVec_sgT, hback', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2

end GlobalTheory.DivTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetVolumeWeightedSumConj
section
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_conj (T L : Subgroup H) (c x : H) :
    GlobalTheory.LKLoc.locPart (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (MulAut.conj c x) = (GlobalTheory.LKLoc.locPart T L x).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.LKLoc.locPart
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, Subgroup.map_map, Subgroup.map_map]
  congr 2
  ext k
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
  group

theorem volRat_conj (U V : Subgroup H) (c : H) :
    GlobalTheory.LKLoc.volRat (U.map (MulAut.conj c).toMonoidHom) (V.map (MulAut.conj c).toMonoidHom) =
      GlobalTheory.LKLoc.volRat U V := by
  unfold GlobalTheory.LKLoc.volRat
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

theorem wt_conj (T L U : Subgroup H) (Ψ : H → ℂ) (c x : H) :
    wt (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (U.map (MulAut.conj c).toMonoidHom) (fun y => Ψ (c⁻¹ * y * c)) (MulAut.conj c x) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_conj, volRat_conj]
  congr 2
  simp only [MulAut.conj_apply]
  group

theorem dsum_conj : ∀ (H : Type) [Group H] (T L U : Subgroup H) (Ψ : H → ℂ) (c : H),
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = GlobalTheory.OrbDesc.dsum (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
    (U.map (MulAut.conj c).toMonoidHom) (fun x => Ψ (c⁻¹ * x * c)) := by
  intro H _ T L U Ψ c hT hΨl hΨr
  set φ := MulAut.conj c with hφ
  have hT' : ∀ s ∈ T.map φ.toMonoidHom, ∀ t ∈ T.map φ.toMonoidHom, s * t = t * s := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hT s hs t ht]
  have hΨl' : ∀ t ∈ T.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (t * x) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨t, ht, rfl⟩ x
    have : c⁻¹ * (φ.toMonoidHom t * x) * c = t * (c⁻¹ * x * c) := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨl t ht]
  have hΨr' : ∀ l ∈ L.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (x * l) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨l, hl, rfl⟩ x
    have : c⁻¹ * (x * φ.toMonoidHom l) * c = (c⁻¹ * x * c) * l := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨr l hl]
  let E : DoubleCoset.Quotient (T : Set H) (L : Set H) ≃
      DoubleCoset.Quotient ((T.map φ.toMonoidHom : Subgroup H) : Set H) ((L.map φ.toMonoidHom : Subgroup H) : Set H) :=
    Quotient.congr φ.toEquiv (by
      intro a b
      rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
      constructor
      · rintro ⟨t, ht, l, hl, rfl⟩
        exact ⟨φ t, ⟨t, ht, rfl⟩, φ l, ⟨l, hl, rfl⟩, by simp [map_mul]⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨l, hl, rfl⟩, h⟩
        refine ⟨t, ht, l, hl, φ.injective ?_⟩
        simpa [map_mul] using h)
  unfold dsum
  rw [← finsum_comp_equiv E]
  congr 1
  ext q
  have hE : E q = DoubleCoset.mk _ _ (φ (Quotient.out q)) := by
    conv_lhs => rw [← DoubleCoset.out_eq' T L q]
    rfl
  rw [hE, wt_out _ hT' hΨl' hΨr', wt_conj]

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
section
open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  obtain ⟨c, hc, e1⟩ := h1
  obtain ⟨d, hd, e2⟩ := h2
  have key : ∀ (c : Fin n → Fin n → ℕ), (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) → ∀ a b : Fin n,
      (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ -(c a b : ℝ) := by
    intro c hc a b
    by_cases h : c a b = 0
    · simp [h]
    · have h3 : (a : ℕ) + 1 ≤ b := (hc a b h).1
      have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hs1 := height_sum c
  have hs2 := height_sum d
  rw [← e1] at hs1
  rw [← e2] at hs2
  have hz : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - μ) i + ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - Λ) i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by simp only [Pi.sub_apply]; ring
  have l1 : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ ∑ a, ∑ b, -(c a b : ℝ) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key c hc a b
  have l2 : ∑ a, ∑ b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ =>
      (key d hd a b).trans (neg_nonpos.2 (Nat.cast_nonneg _))
  simp only [Finset.sum_neg_distrib] at l1
  have l3 : ∑ a, ∑ b, (c a b : ℝ) ≤ 0 := by linarith
  have hc0 : ∀ a b, (c a b : ℝ) = 0 := by
    intro a b
    refine le_antisymm (le_trans ?_ l3) (Nat.cast_nonneg _)
    calc (c a b : ℝ) ≤ ∑ b, (c a b : ℝ) :=
          Finset.single_le_sum (f := fun b => (c a b : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ b)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, (c a b : ℝ))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ a)
  simp only [hc0, zero_smul, Finset.sum_const_zero] at e1
  exact (sub_eq_zero.1 e1).symm

end GlobalTheory.LowHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjLocal

section Field

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem val_unif : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) := by
  have h := Formalism.L2.Host.unif_spec P
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h

theorem mk_unit {u : E} (hu : P.valuation E u = 1) : FinitePlace.mk P u = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]
  simp

theorem mk_unif : FinitePlace.mk P ((Formalism.L2.Host.unif P : Eˣ) : E) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

end Field

variable {D : D7}

noncomputable def locHom {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ where
  toFun := locU he
  map_one' := Units.ext (by rw [locU_val]; simp [locE])
  map_mul' k l := Units.ext (by rw [Units.val_mul, locU_val, locU_val, locU_val, locE_mul_locE he, Units.val_mul])

theorem locE_parts {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (u : D.host.E)
    (hu : P.valuation D.host.E u ≤ 1) : infPart D (locE D e u) = 1 ∧ finPart D (locE D e u) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩
  rw [hint]
  intro Q
  have h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u := hι u
  have h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1) :=
    GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5, h4]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu
  · rw [h3 Q hQ]
    simp

end GlobalTheory.EtaConjLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalAffineIndEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.LocGlobIndEt

theorem eqv_of_comp_iso {R : Type} [CommRing R] {E E' E'' : Spc} (g : E ⟶ E') (e : E' ⟶ E'') [IsIso e] (F : Shv R)
    (h : Eqv R (g ≫ e) F) : Eqv R g F := by
  intro n
  have he : Function.Bijective (pull R e F n) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv e) F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    · rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  refine (Function.Bijective.of_comp_iff (pull R g F n) he).1 ?_
  have : (⇑(pull R g F n) ∘ ⇑(pull R e F n)) = ⇑(pull R (g ≫ e) F n) := funext fun x => (pull_comp R g e F n x).symm
  rw [this]
  exact h n

theorem main : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f]
    [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A →
      Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) →
    Eqv _ (sch.map f) (tw q i) := by
  intro q B _ Y f _ _ _ i hyp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y (Spec (CommRingCat.of B)) (Spec (CommRingCat.of B)) f
    (𝟙 _) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hind, rfl⟩ := isStalk_affine B O s hs
  have key := @hyp O _ inst hSH hind
  refine eqv_of_comp_iso _ (sch.map (pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B O))))) _ ?_
  rw [← sch.map_comp, pullback.lift_snd, Category.comp_id]
  generalize hf : f ≫ 𝟙 _ = f'
  rw [Category.comp_id] at hf
  subst hf
  exact key

end GlobalTheory.LocGlobIndEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) → (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  first | (exact @GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (exact GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (intros; apply GlobalTheory.EtC.CechDescHInv.hInv_of_integral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSide_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  first | exact @GlobalTheory.AdelicSide.exists_thAd_of_models | exact GlobalTheory.AdelicSide.exists_thAd_of_models | (intros; apply GlobalTheory.AdelicSide.exists_thAd_of_models <;> assumption)
end

