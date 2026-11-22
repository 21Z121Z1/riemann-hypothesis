import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquivStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_numberField_of_continuous_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  first | exact @GlobalTheory.approx_of_completion_equiv | exact GlobalTheory.approx_of_completion_equiv | (intros; apply GlobalTheory.approx_of_completion_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_unique_of_inductive : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  first | exact @GlobalTheory.WeilBrauer.eq_of_induced | exact GlobalTheory.WeilBrauer.eq_of_induced | (intros; apply GlobalTheory.WeilBrauer.eq_of_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfApproxByCongruentGlobalUnitsStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_approx_by_congruent_global_units : ChevalleyUnits → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E), Valued.v x = 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → x = 1 := by
  first | exact @GlobalTheory.eq_one_of_approx_by_congruent_units | exact GlobalTheory.eq_one_of_approx_by_congruent_units | (intros; apply GlobalTheory.eq_one_of_approx_by_congruent_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Maps (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (V : Submodule ℂ (Sm E a)) (hs : IsStable V) (hi : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) : ⨆ f : Maps V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps V w σ) v, act o (f.1 v) ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hs o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps V w σ) ⟨v, rfl⟩
  refine (hi _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (⨆ f : Maps V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w
            (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, h1, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, h1, hf⟩ : Maps V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem exists_comp_ne_zero (V : Submodule ℂ (Sm E a)) (hs : IsStable V) (hi : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) {X : Type} [AddCommGroup X] [Module ℂ X] (β : V →ₗ[ℂ] X) (hβ : β ≠ 0) :
    ∃ f : Maps V w σ, β ∘ₗ f.1.codRestrict V f.2.1 ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hβ (LinearMap.ext fun φ => ?_)
  have hle : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (LinearMap.ker β).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, LinearMap.congr_fun (hc f) v, rfl⟩
  rw [iSup_range_eq V hs hi w σ h] at hle
  obtain ⟨ψ, h1, h2⟩ := hle φ.2
  obtain rfl : ψ = φ := Subtype.ext h2
  exact h1

theorem equiv_contra_locComp : IrreducibleAdmissibleGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (V : Submodule ℂ (Sm E a)), IsStable V → (∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V) → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))), GlobalTheory.UnitaryBC.IsLocCompGL V w σ → ∀ β : V →ₗ[ℂ] σ'.V →ₗ[ℂ] ℂ, β ≠ 0 → (∀ (g : GL (Fin a) (w.adicCompletion E)) (φ ψ : V) (v : σ'.V), ψ.1 = finRep E a (locGL E a w g) φ.1 → β ψ (σ'.ρ g v) = β φ v) → Nonempty (σ'.ρ.Equiv (GlobalTheory.SmGL.contra σ.ρ)) := by
  intro hadm E _ _ _ a V hs hi w σ σ' h β hβ hinv
  obtain ⟨f, hf⟩ := exists_comp_ne_zero V hs hi w σ h β hβ
  have hB : ∀ g u v, (β ∘ₗ f.1.codRestrict V f.2.1) (σ.ρ g u) (σ'.ρ g v) = (β ∘ₗ f.1.codRestrict V f.2.1) u v :=
    fun g u v => hinv g _ _ v (f.2.2 g u)
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ a)
      (hadm _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  exact ⟨(GlobalTheory.InvPairing.pairMap σ.ρ σ'.smooth _ hB).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ σ'.smooth _ hB hf σ'.irred hirr)⟩

end GlobalTheory.LocDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisIntegralCoords
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.SingleDatum

theorem exists_basis_integral_coords : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (O : Subring ℂ), (∀ x : F, la.valuation F x ≤ 1 → (x : ℂ) ∈ O) → ∀ S : Set ℂ, S.Finite → S ⊆ O → ∃ (m : ℕ) (β : Fin m → ℂ) (lam : Fin m → (ℂ →ₗ[F] F)), (∀ k, β k ∈ O) ∧ ∀ x ∈ S, x = ∑ k, β k * (lam k x : ℂ) ∧ ∀ k, la.valuation F (lam k x) ≤ 1 := by
  intro F _ la O hO S hS hSO
  let R := (la.valuation F).integer
  have hsm : ∀ (r : R) (z : ℂ), r • z = (((r : F) : ℂ)) * z := fun r z => rfl
  let N : Submodule R ℂ := Submodule.span R S
  haveI : Module.Finite R N := Module.Finite.span_of_finite R hS
  haveI : Module.IsTorsionFree R N := inferInstance
  haveI : Module.Free R N := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)
  let m := Fintype.card (Module.Free.ChooseBasisIndex R N)
  let β : Fin m → ℂ := fun k => ((b k : N) : ℂ)
  have hliR : LinearIndependent R β := b.linearIndependent.map' N.subtype N.ker_subtype
  have hliF : LinearIndependent F β := (LinearIndependent.iff_fractionRing R F).1 hliR
  choose g hg using fun k : Fin m => LinearMap.exists_extend ((Finsupp.lapply k).comp hliF.repr)
  have key : ∀ k j, g k (β j) = if j = k then 1 else 0 := by
    intro k j
    have hmem : β j ∈ Submodule.span F (Set.range β) := Submodule.subset_span ⟨j, rfl⟩
    have := LinearMap.congr_fun (hg k) ⟨β j, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hliF.repr_eq_single j _ rfl]
    simp [Finsupp.single_apply]
  have hNO : ∀ z ∈ N, z ∈ O := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hSO hy
    | zero => exact O.zero_mem
    | add y w _ _ hy hw => exact O.add_mem hy hw
    | smul r y _ hy =>
      rw [hsm]
      exact O.mul_mem (hO _ ((Valuation.mem_integer_iff _ _).1 r.2)) hy
  refine ⟨m, β, g, fun k => hNO _ (b k).2, ?_⟩
  intro x hx
  have hxN : x ∈ N := Submodule.subset_span hx
  let c : Fin m → F := fun j => ((b.repr ⟨x, hxN⟩ j : R) : F)
  have hxs : x = ∑ j, c j • β j := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hxN⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Submodule.coe_smul, hsm, Algebra.smul_def]
    rfl
  have hg' : ∀ k, g k x = c k := by
    intro k
    rw [hxs, map_sum]
    simp only [map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨?_, fun k => ?_⟩
  · conv_lhs => rw [hxs]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg', Algebra.smul_def, mul_comm]
    rfl
  · rw [hg']
    exact (Valuation.mem_integer_iff _ _).1 (b.repr ⟨x, hxN⟩ k).2

end GlobalTheory.SingleDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WPre

theorem map_smul_hom {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S] {m n : Type*}
    (f : F) (c : R) (M : Matrix m n R) : (c • M).map f = f c • M.map f :=
  Matrix.ext fun i j => by simp

theorem smul_cancel {R : Type*} [CommRing R] {m n : Type*} {c : R} (hc : IsUnit c) {M M' : Matrix m n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

end GlobalTheory.BKLim.WPre

namespace GlobalTheory.BKLim

open GlobalTheory.BKLim.WPre in

theorem exists_pre_of_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  intro l _ K bk τ hτ d ρ hρ s
  classical
  obtain ⟨Y, Z, b, A, A', hYu, hZu, hWZ, hAA', hφY⟩ := GlobalTheory.T.exists_finiteHeight_breuilKisin_lattice_semistable l K bk τ hτ d ρ hρ s
  obtain ⟨htu, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  obtain ⟨hmaps, hgal, -, h0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i0, hi0⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  have hinj : Function.Injective bk.iA := GlobalTheory.BSP.SeedAsm.iA_injective bk
  obtain ⟨u, hu⟩ := htu
  set n := s.N with hn
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  set T : Matrix (Fin d) (Fin d) (WCb l) := (u⁻¹ ^ n : (WCb l)ˣ) • Y.map (inclW l) with hT
  have hYT : Y.map (inclW l) = t ^ n • T := by
    rw [hT, Units.smul_def, smul_smul, ← hu, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have htn : IsUnit (t ^ n) := by rw [← hu]; exact (Units.isUnit u).pow n

  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hφT : e ^ n • T.map (frobW l) = T * A.map bk.evW := by
    have h1 := congrArg (fun M => Matrix.map M (inclW l)) hφY
    simp only [Matrix.map_mul] at h1
    have h2 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [GlobalTheory.Prism.frobW_inclW]
    rw [h2, hYT, show (A.map bk.ev).map (inclW l) = A.map bk.evW from rfl] at h1
    apply smul_cancel htn
    calc t ^ n • e ^ n • T.map (frobW l) = (t ^ n • T).map (frobW l) := by
          rw [map_smul_hom, map_pow, hft, mul_pow, mul_comm, smul_smul]
      _ = t ^ n • (T * A.map bk.evW) := by rw [h1, Matrix.smul_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
    intro g hg
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ h0 (g : GQ l)
    obtain ⟨hGfix, hGW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR
    have hGZ : (Z.map i0).map G = Z.map i0 := by
      exact Matrix.ext fun i j => hGfix i0 hi0 _
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = (Y.map bk.iA).map G := by
      exact Matrix.ext fun i j => (hG.ext _).symm
    have hA1 : (τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map bk.iA =
        (Per.σA (g : GQ l) τ ^ n • Y).map bk.iA := by
      rw [map_smul_hom, map_smul_hom, Matrix.map_mul, hYG, ← hWZ i0 hi0, Matrix.map_mul, hGZ, map_pow, map_pow,
        show ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA = R from Matrix.ext fun i j => rfl, ← Matrix.mul_assoc,
        ← Matrix.smul_mul, hGW, Matrix.smul_mul, ← hG.ext]
    have hA2 : τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
        Per.σA (g : GQ l) τ ^ n • Y := by
      refine Matrix.ext fun i j => hinj ?_
      have := congrFun (congrFun hA1 i) j
      simpa only [Matrix.map_apply] using this
    have hA3 := congrArg (fun M => Matrix.map M (inclW l)) hA2
    simp only [map_smul_hom, Matrix.map_mul, map_pow] at hA3
    have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
      exact Matrix.ext fun i j => (inclWA l).commutes _
    have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      exact Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
    rw [hz, hg', hYT, map_smul_hom, map_pow, ht, GlobalTheory.Prism.galW_inclW] at hA3
    have hsu : IsUnit (inclW l (Per.σA (g : GQ l) τ) ^ n) := (hστ _).pow n
    apply smul_cancel (htn.mul hsu)
    have e1 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • (zW (ρ g) * T.map (galW l (g : GQ l))) =
        t ^ n • (zW (ρ g) * (inclW l (Per.σA (g : GQ l) τ) ^ n • T.map (galW l (g : GQ l)))) := by
      rw [Matrix.mul_smul, smul_smul]
    have e2 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • T = inclW l (Per.σA (g : GQ l) τ) ^ n • t ^ n • T := by
      rw [smul_smul, mul_comm]
    rw [e1, e2]
    exact hA3
  refine ⟨n + b, Pre.mk T ?_ (bk.E ^ b • A) (bk.E ^ (2 * n) • A') ?_ ?_ hfix, Y, Z, hYT, hZu, hWZ⟩
  · rw [hT]; exact hYu.smul _
  · rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  · rw [map_smul_hom, Matrix.mul_smul, ← hφT, pow_add, mul_comm, ← smul_smul, map_pow]

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproductStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparison_matrix_prismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)), ∃ ε : Matrix (Fin d) (Fin d) En.Q.A, ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.exists_rel_env | exact GlobalTheory.BSP.Height.exists_rel_env | (intros; apply GlobalTheory.BSP.Height.exists_rel_env <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjLatUnimodBd
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatSplit

open GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.UnRep.SmallMat

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_conjLat_unimod_bd (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ)
    (h : GL (Fin n) (RA (maximalRealSubfield E) E)) (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hs : SuppSplit (IsCMField.complexConj E) bad h.1) :
    ∃ (Λ : Submodule (𝓞 E) (Fin n → E)) (k : ℕ),
      (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (Formalism.L2.Pj.stdLat E n) ∧ (conjLat H Λ).Unimod ∧
      k.Coprime bad ∧ ∀ u : ℕ, Ideal.span {((u * k : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ Formalism.L2.Pj.stdLat E n ∧
        Ideal.span {((u * k : ℕ) : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ (conjLat H Λ).La := by
  obtain ⟨-, -, hfg, hsp, -⟩ := StdInhab.main E H n
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf (maximalRealSubfield E) E n (Formalism.L2.Pj.stdLat E n) h hfg hsp
  obtain ⟨e, -, -, he, hcut⟩ := hs
  have hcut' := cut_inv h _ hcut
  have he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ((bad : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut
  obtain ⟨t', ht', hb'⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut'
  refine ⟨Λ, t' * t, hΛ, conjLat_unimod H hh hΛ, Nat.Coprime.mul_left ht' ht, fun u => ?_⟩
  refine conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)
  · have := hb.mul ((u * t' : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc] at this
  · have := hb'.mul ((u * t : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc, mul_comm t] at this

end General

end GlobalTheory.ConjLatSplit

open GlobalTheory.ConjLatSplit in

theorem GlobalTheory.SingleDatum.exists_conjLat_levOK : ∀ (D : D7) (V : HSp D), V.gram = 1 → L0c D V = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → ∀ (bad M p : ℕ), Odd M → 2 ∣ bad → M ∣ bad → p ∣ bad → ∀ h : GA D V, SplitOffBad V bad h → ∃ (Λ : GenLat D.host.E V.rank) (u : ℕ), (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) ∧ Λ.Unimod ∧ Λ.TrivAt M ∧ Nat.Coprime u p ∧ Λ.LevOK (M * u) M := by
  intro D V hg hL0 bad M p hM h2 hMb hpb h hs
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank :=
    SetLike.coe_injective ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans hL0)
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  have hu := GlobalTheory.UnRep.Space.isUnA_finHom V h
  rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc] at hu
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) bad (finHom V h).1 :=
    (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1 (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  rw [hc] at hs'
  obtain ⟨Λ, k, h1, hU, hk, hnat⟩ := exists_conjLat_unimod_bd (Formalism.L2.Pj.hostOfRecord D) bad (finHom V h) hu hs'
  rw [GlobalTheory.SplitReps.hLat_one] at hL
  have e := GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Λ (by rw [hL]; exact h1)
  have hk1 := hnat 1
  rw [one_mul] at hk1
  refine ⟨GlobalTheory.UnRep.FullReps.conjLat (Formalism.L2.Pj.hostOfRecord D) Λ, k, fun v => ?_, hU,
    ⟨k, hk.coprime_dvd_right hMb, hk1⟩, hk.coprime_dvd_right hpb,
    ⟨hM.mul (Nat.Coprime.odd_of_right (hk.coprime_dvd_right h2)), dvd_mul_right _ _,
      le_inf (hnat M).2 Submodule.smul_le_right⟩⟩
  change _ ↔ _ ∈ Bridge.hLat V (FWT.fin V h)
  rw [e]
  exact Iff.rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 := by
  first | exact @GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | exact GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | (intros; apply GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_frame_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F hDR
  obtain ⟨P, r, hP⟩ := GlobalTheory.T.exists_breuilKisin_basis_limit_lattice l K bk τ hτ d N ρ tw (fun n => (F n).toPre)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe l K bk d N ρ tw F P r hP
  have hL : ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
    subst hF₀
    exact hP
  exact ⟨F₀, GlobalTheory.T.isDR_of_links' l K bk d N ρ tw F F₀ r hL hDR,
    fun hCr => GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower l K bk d N ρ tw F F₀ r hL hCr, r, hL⟩

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicFrameLagrangianFirstSummandStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧ Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  first | exact @GlobalTheory.RawLift.exists_isoFrame_comap_inl | exact GlobalTheory.RawLift.exists_isoFrame_comap_inl | (intros; apply GlobalTheory.RawLift.exists_isoFrame_comap_inl <;> assumption)
end

