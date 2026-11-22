import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0153
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomo
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU E n ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finset_sum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU E n, opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU E n).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.TwistLetters

set_option maxHeartbeats 4000000 in

theorem wdSpace_twist_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m _ _ _ hs hm ht
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v = χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  clear_value χ
  have hl := dmul_mulD_left P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hr := dmul_mulD_right P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hL1 := @GlobalTheory.T.exists_balancedBilinear_tensorProduct_map _ _ _ _ _ _ _ _ _ _ _ _ _ (mulD P (Bw.repE L s)) (mulD P (Bw.repE L m)) (mulD P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) ℂ _ (algC ι L) (urC ι) _ hl hr
  obtain ⟨Φ, hΦ'⟩ : ∃ Φ : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), ∀ x y, Φ (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) = wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) := hL1
  have hsurj : Function.Surjective Φ := by
    have h2b := GlobalTheory.T.exists_invertible_dPst_potSemistableCharacter P AI hT (Bw.repE L m) χ hχm hm
    obtain ⟨y, hy, y', hyy'⟩ := h2b
    let y₀ : ↥(Dpst P (Bw.repE L m)) := ⟨y, hy⟩
    have h2 := GlobalTheory.T.exists_periodProduct_eq_of_invertible_character P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt y₀ y' hyy'
    have hspan : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) = ⊤ := span_wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
    have hle : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := h2 z
      exact ⟨_, (hΦ' x y₀).trans (by rw [hx])⟩
    intro z
    exact LinearMap.mem_range.mp (hle (Submodule.eq_top_iff'.mp hspan z))
  have hdim : Module.finrank ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m)) =
      Module.finrank ℂ (WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) := by
    rw [Module.finrank_tensorProduct, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hs,
      GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hm, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ ht]
    simp
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have key : ∀ {f g : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))},
      (∀ x y, f (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) =
        g (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y)) → f = g := by
    intro f g H
    apply TensorProduct.ext
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L s))
    intro x
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L m))
    intro y
    exact H x y
  have hW : ∀ σ x y, weilD Bw h P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) =
      (dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) (weilD Bw h P (Bw.repE L s) σ x) (weilD Bw h P (Bw.repE L m) σ y) := by
    intro σ x y
    simp only [weilD_apply, Module.End.mul_apply, GlobalTheory.T.periodProduct_commutes_frobenius_zpow P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt, actD_dmul]
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun σ x => ?_, fun x => ?_⟩
  · have e : Φ ∘ₗ TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) =
        wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, wdRho_mk, hΦ', hW]
    exact LinearMap.congr_fun e x
  · have e : Φ ∘ₗ ((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) +
        (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s))) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        wdN_mk, map_add, hΦ', monD_dmul, wdMk_add]
    exact LinearMap.congr_fun e x

end GlobalTheory.Pst.TwistLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameterStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  first | exact @GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | exact GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | (intros; apply GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGaloisCharacterOfAlgebraic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalPin
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.CuspRep Formalism.BasicNotions.Loc

theorem heckeLAdicTwist : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.HeckeLAdicParameterAbove → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (i : D.nd.Loc) (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))) := by
  intro hF hGA hCh hPa hL D P i χ s hint
  have := host_isCMField D.host
  set ψ : HChar D.host.E := (P.chr.e1 χ).1 with hψ
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  have hinf : ∀ τ, D.naut.infG χ τ = {expo ψ τ} := fun τ => by
    rw [P.cg.inf, CGu.infChar, GlobalTheory.T.cusp_rep_one_eq_of_character hF hL D P χ, CG.infChar_ofChar]
  have hexpo : ∀ τ, expo (ψ * ν) τ = expo ψ τ + s := fun τ => by
    have h := (CG.hasInfChar_ofChar ψ τ).twist ν
    rw [CG.twist_ofChar, Multiset.map_singleton] at h
    have := h.infChar_eq
    rw [CG.infChar_ofChar] at this
    rw [← (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
    simpa using this
  have hint' : ∀ τ, ∃ k : ℤ, expo (ψ * ν) τ = k := fun τ => by
    obtain ⟨k, hk⟩ := hint τ (expo ψ τ) (by rw [hinf]; exact Multiset.mem_singleton_self _)
    exact ⟨k, by rw [hexpo, hk]⟩
  choose n hn using hint'
  have hAlg : IsAlgPos (ψ * ν) n := GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo D.host.E (ψ * ν) n hn
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf (D.naut.iotaQC i) hAlg
  have hpar : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG χ w) u) =
      (ParLaws.locPar hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, ← GlobalTheory.T.cusp_rep_one_eq_of_character hF hL D P χ]
    rfl
  have htw : ∀ w : PlE D.host, ParLaws.locPar hL (CG.ofChar (ψ * ν)) (D.nd.plOm.2 w) =
      (ParLaws.locPar hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw s := fun w => by
    rw [← CG.twist_ofChar]
    exact Blocks.locPar_twist_absPow hL hF _ hν _
  refine ⟨rk1 μ, ?_, fun w hw => ?_, fun w hw => ?_⟩
  · show Continuous fun g => ((rk1 μ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))
    exact (continuous_pi fun _ => Units.continuous_val.comp hμc).matrix_diagonal
  · have hl : (((D.nd.l i : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := hw
    rw [(P.wdOf i 1 (rk1 μ) w).1]
    refine (P.T.e w).injective ?_
    rw [P.wd.away _ _ (rk1 μ) w hl, GlobalTheory.T.weil_deligne_rank_one_local_param hL D.host.E D.nd.Om _ _ art ha _ n μ hμc hμ _ w (D.nd.plOm.2 w) hl, htw, hpar]
  · have hab := fun (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
        (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O) (hj : Induces Bw) =>
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hCh) D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
        (D.naut.iotaQC i) art ha (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) O Bw hj
    obtain ⟨hdR, hJ⟩ := GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) μ hμc
      (fun τ => {-n ((D.naut.iotaQC i).toRingHom.comp τ)}) w hw
      (fun O _ _ _ Bw hj => ⟨(hab O Bw hj).1, (hab O Bw hj).2.2.2⟩)
    refine ⟨(P.wdOf i 1 (rk1 μ) w).2.2.2.1.2 hdR, ?_, fun τ hτ => ?_⟩
    · rw [(P.wdOf i 1 (rk1 μ) w).1]
      refine (P.T.e w).injective ?_
      obtain ⟨LL, Bw, hj, he⟩ := P.wd.above _ _ (rk1 μ) w hw
      have hc : IsComp (ψ * ν) w ((ψ * ν).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
      rw [he, hpar, ← htw, hPa D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩ (D.naut.iotaQC i) art ha
        (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hj _ hc _
        (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)), ParLaws.locPar_ofChar]
      rfl
    · rw [(P.wdOf i 1 (rk1 μ) w).2.2.2.2 τ, hJ τ hτ, hinf, Multiset.map_singleton, Multiset.map_singleton,
        Int.cast_neg, ← hn, hexpo]
end GlobalTheory.GalPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSemisimpleGaloisRepWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.BCGalAll

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  intro D h0 h2 i P Pa hB
  obtain ⟨ρ, hc, hs, hw, hl⟩ := GlobalTheory.T.exists_galois_rep_base_change D h0 h2 i P Pa hB
  refine ⟨ρ, hc, hs, fun w _ => hw w, fun w hw' => ⟨(hl w hw').1, hw w, fun τ hτ => ?_⟩⟩
  apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
  rw [(hl w hw').2 τ hτ, D.naut.locAut_hodgeTateWeightsLevelZero_def i τ]

end GlobalTheory.BCGalAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivOutside_inertDatum_local_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (k : GL (Fin n) (w.adicCompletion L)), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k := by
  first | exact @GlobalTheory.InertLift.exists_trivOutside_loc_eq | exact GlobalTheory.InertLift.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.InertLift.exists_trivOutside_loc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPlaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n), ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  first | exact @GlobalTheory.PlaceDecomp.decomp | exact GlobalTheory.PlaceDecomp.decomp | (intros; apply GlobalTheory.PlaceDecomp.decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  first | exact @GlobalTheory.FinTypSpanLoc.main | exact GlobalTheory.FinTypSpanLoc.main | (intros; apply GlobalTheory.FinTypSpanLoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisWeightEqDimSubOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CsdWeight

theorem sum_map_const_sub (c : ℂ) (m : Multiset ℂ) :
    (m.map fun z => c - z).sum = (Multiset.card m : ℂ) * c - m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]; push_cast; ring

theorem weight_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
    (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → π.IsCsd → IsGalRepOf π χ ι r wt HT → wt = (a : ℤ) - 1 := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ r wt HT hinf hc H
  obtain ⟨φ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  set τ0 : E →+* Qbar l := ι.symm.toRingHom.comp φ0 with hτ0
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hcdef
  set φ : E →+* ℂ := ι.toRingHom.comp τ0 with hφ
  have hconj : ι.toRingHom.comp (τ0.comp c) = ComplexEmbedding.conjugate φ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E φ x
  obtain ⟨m, hm⟩ := hinf φ
  obtain ⟨m', hm'⟩ := hinf (ComplexEmbedding.conjugate φ)
  have hmm := GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd E a π hc φ m m' hm hm'
  have i1 : (CG.mk π).infChar φ = m := CG.HasInfChar.infChar_eq (π := CG.mk π) hm
  have i2 : (CG.mk π).infChar (ComplexEmbedding.conjugate φ) = m' := CG.HasInfChar.infChar_eq (π := CG.mk π) hm'
  have hcard : Multiset.card m = a := i1 ▸ CG.card_infChar _ φ
  have e1 := congrArg Multiset.sum (H.weights τ0)
  have e2 := congrArg Multiset.sum (H.weights (τ0.comp c))
  rw [H.weights_conj τ0, hconj, i2, hmm] at e2
  rw [i1] at e1
  rw [sum_map_const_sub, hcard] at e1
  rw [sum_map_const_sub, Multiset.card_map, hcard] at e2
  have e3 : (((HT τ0).map (wt - ·)).map fun n : ℤ => (n : ℂ)).sum =
      (Multiset.card (HT τ0) : ℂ) * wt - ((HT τ0).map fun n : ℤ => (n : ℂ)).sum := by
    rw [Multiset.map_map]
    have : ((HT τ0).map ((fun n : ℤ => (n : ℂ)) ∘ (wt - ·))) = ((HT τ0).map fun n : ℤ => (n : ℂ)).map
        fun z => (wt : ℂ) - z := by
      rw [Multiset.map_map]; refine Multiset.map_congr rfl fun n _ => ?_; simp
    rw [this, sum_map_const_sub, Multiset.card_map]
  have hcHT : Multiset.card (HT τ0) = a := by
    have := congrArg Multiset.card (H.weights τ0)
    rwa [Multiset.card_map, Multiset.card_map, i1, hcard] at this
  rw [e3, hcHT, e1, Multiset.sum_map_neg'] at e2
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have h4 : (a : ℂ) * ((wt : ℂ) - ((a : ℂ) - 1)) = 0 := by linear_combination e2
  have h5 : (wt : ℂ) = ((a : ℤ) - 1 : ℤ) := by
    push_cast
    have := (mul_eq_zero.1 h4).resolve_left ha0
    linear_combination this
  exact_mod_cast h5

end GlobalTheory.CsdWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  first | exact @GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | exact GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | (intros; apply GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeStandardTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_standard_twist : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), HeckeStdTw P.H.cover.B := by
  first | exact @GlobalTheory.NPin.heckeStdTw_cover | exact GlobalTheory.NPin.heckeStdTw_cover | (intros; apply GlobalTheory.NPin.heckeStdTw_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ISupIndepOfPairwiseOrthogonalDefiniteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' := by
  first | exact @GlobalTheory.petersson_form_classSum_comparison | exact GlobalTheory.petersson_form_classSum_comparison | (intros; apply GlobalTheory.petersson_form_classSum_comparison <;> assumption)
end

