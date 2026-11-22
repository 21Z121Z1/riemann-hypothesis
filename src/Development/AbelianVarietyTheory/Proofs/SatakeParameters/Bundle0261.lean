import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normV_eq_normV_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | exact GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | (intros; apply GlobalTheory.AboveL.ResDeg.normV_eq_under_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZeroStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Continuous r → ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  first | exact @GlobalTheory.AboveL.exists_open_trace_ne_zero | exact GlobalTheory.AboveL.exists_open_trace_ne_zero | (intros; apply GlobalTheory.AboveL.exists_open_trace_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroupStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → ∃ N : Subgroup (G F Ω), N.Normal ∧ IsOpen (N : Set (G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  first | exact @GlobalTheory.OpenNormal.exists_open_normal_le | exact GlobalTheory.OpenNormal.exists_open_normal_le | (intros; apply GlobalTheory.OpenNormal.exists_open_normal_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | (exact @GlobalTheory.SplitComp.exists_comp_and_unique) | (exact GlobalTheory.SplitComp.exists_comp_and_unique) | (intros; apply GlobalTheory.SplitComp.exists_comp_and_unique  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevelsStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_fixed_by_product_localLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w a) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.FixProd.fix_prod) | (exact GlobalTheory.Cong.FixProd.fix_prod) | (intros; apply GlobalTheory.Cong.FixProd.fix_prod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotientStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_decompositionGroups_cover_openQuotient : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  first | exact @GlobalTheory.DecCover.main | exact GlobalTheory.DecCover.main | (intros; apply GlobalTheory.DecCover.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU E a) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  have hinf : cInf x = 1 := MonoidHom.mem_ker.1 hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

theorem isCompact_integral :
    IsCompact {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} := by
  have e' : ∀ k : finU E a, k ∈ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap
      (GlobalTheory.BCT.GlobLev.finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
    intro k
    rw [Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  have e : {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} =
      ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
        Set (finU E a)) := by
    ext k
    exact (e' k).symm
  have hO : IsOpen ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
      Set (finU E a)) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  rw [e]
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
      ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E a).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart E a x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_finite_fix {φ : UA E a → ℂ} (hφ : IsAutFormU φ) :
    ∃ t : Finset (HeightOneSpectrum (𝓞 E)), ∀ k ∈ finU E a, (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u a) →
      (∀ u ∈ t, cLoc u k = 1) → RU E a k φ = φ := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) := fun u =>
    Units.isEmbedding_embedProduct.t2Space
  have hc := (isCompact_integral (E := E) (a := a)).diff hφ.level
  have hcov : {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} \ {k : finU E a | RU E a k φ = φ} ⊆
      ⋃ u, {k : finU E a | cLoc u k.1 ≠ 1} := by
    rintro k ⟨-, hk⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hne
    push_neg at hne
    apply hk
    show RU E a k.1 φ = φ
    rw [eq_one_of_forall_cLoc k.2 hne, map_one]
    rfl
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun u => isOpen_ne_fun
    ((GlobalTheory.BCT.GlobLev.continuous_cLoc u).comp continuous_subtype_val) continuous_const) hcov
  refine ⟨t, fun k hk hint h1 => ?_⟩
  by_contra hne
  have := ht (show (⟨k, hk⟩ : finU E a) ∈ _ from ⟨hint, hne⟩)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨u, hu, hne'⟩ := this
  exact hne' (h1 u hu)

theorem one_of_cLoc_eq_one {q : HeightOneSpectrum (𝓞 E)} {z : UA E a} (h : cLoc q z = 1) :
    ∀ u, ¬ Apart u q → cLoc u z = 1 := by
  intro u hu
  by_cases hq : IsSplitAt q
  · exact GlobalTheory.Cong.LevelExt.one_of_cLoc hq z h u hu
  · rw [eq_of_not_apart_of_not_split hq hu]
    exact h

theorem peel (φ : UA E a → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ k ∈ finU E a, (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u a) → (∀ u ∈ S, cLoc u k = 1) → RU E a k φ = φ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ x ∈ finU E a, (∀ u, (∀ q ∈ Q, Apart u q) → (u ∈ S → cLoc u x = 1) ∧ cLoc u x ∈ GlobalTheory.LFun.KGL u a) →
      (∀ q ∈ Q, ∃ y ∈ locU a q, RU E a y φ = φ ∧ cLoc q y = cLoc q x) → RU E a x φ = φ := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro x hx h1 _
    exact hS x hx (fun u => (h1 u (by simp)).2) (fun u hu => (h1 u (by simp)).1 hu)
  | @insert q Q hqQ ih =>
    intro x hx h1 h2
    obtain ⟨y, hyl, hyφ, hyq⟩ := h2 q (Finset.mem_insert_self q Q)
    have hyf : y ∈ finU E a := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).1
    have hya : ∀ u, Apart u q → cLoc u y = 1 := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2
    have hq1 : cLoc q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    have hfib : ∀ u, ¬ Apart u q → cLoc u (y⁻¹ * x) = 1 := one_of_cLoc_eq_one hq1
    have happ : ∀ u, Apart u q → cLoc u (y⁻¹ * x) = cLoc u x := fun u hu => by
      rw [map_mul, map_inv, hya u hu, inv_one, one_mul]
    have key : RU E a (y⁻¹ * x) φ = φ := by
      refine ih (y⁻¹ * x) (mul_mem (inv_mem hyf) hx) (fun u hu => ?_) (fun q' hq' => ?_)
      · by_cases huq : Apart u q
        · rw [happ u huq]
          exact h1 u (fun p hp => by
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact huq
            · exact hu p hp)
        · rw [hfib u huq]
          exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
      · by_cases hqq : Apart q' q
        · obtain ⟨y', hy'l, hy'φ, hy'q⟩ := h2 q' (Finset.mem_insert_of_mem hq')
          exact ⟨y', hy'l, hy'φ, hy'q.trans (happ q' hqq).symm⟩
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl, by rw [map_one, hfib q' hqq]⟩
    have hxe : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [hxe, map_mul, Module.End.mul_apply, key, hyφ]

end GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLevFix in

theorem GlobalTheory.Cong.AdaptLev.fixed_of_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  intro E _ _ _ a w₀ H hHle _ _ _ hcof φ hφ hfix x hx
  classical
  obtain ⟨t, ht⟩ := exists_finite_fix hφ
  have hT : {w | ¬ H w = intU a w}.Finite := Filter.eventually_cofinite.1 hcof
  let Q : Finset (HeightOneSpectrum (𝓞 E)) := (t ∪ hT.toFinset).filter (fun w => Apart w w₀)
  obtain ⟨hxf, hx1, hxH⟩ := mem_levelOf.1 hx
  refine peel φ (t : Set _) (fun k hk hi h1 => ht k hk hi h1) Q x hxf (fun u hu => ?_) (fun q hq => ?_)
  · by_cases hu0 : Apart u w₀
    · have huQ : u ∉ Q := fun h => hu u h rfl
      have hut : u ∉ t := fun h => huQ (Finset.mem_filter.2 ⟨Finset.mem_union_left _ h, hu0⟩)
      have huT : H u = intU a u := by
        by_contra h
        exact huQ (Finset.mem_filter.2 ⟨Finset.mem_union_right _ (hT.mem_toFinset.2 h), hu0⟩)
      obtain ⟨y, hy, hyx⟩ := hxH u hu0
      rw [huT] at hy
      refine ⟨fun h => absurd h hut, ?_⟩
      rw [← hyx]
      exact (mem_intU.1 hy).2 u (fun h => h rfl)
    · rw [hx1 u hu0]
      exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
  · have hq0 : Apart q w₀ := (Finset.mem_filter.1 hq).2
    obtain ⟨y, hy, hyx⟩ := hxH q hq0
    exact ⟨y, hHle q hy, hfix q hq0 y hy, hyx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  first | exact @GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | exact GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | (intros; apply GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_norm_descent : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  first | exact @GlobalTheory.RealNormChar.main | exact GlobalTheory.RealNormChar.main | (intros; apply GlobalTheory.RealNormChar.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem tw_cut_eig (s : Bool) {E I C : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hs : (⨆ c, Ec c) = LinearMap.range e) (hl : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) ∧
      ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
        Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) Q =
          Tw.sub s (⨆ (c : C) (_ : Q (fun i => cj s (lab c i))), Ec c) := by
  obtain ⟨hc, hq⟩ := GlobalTheory.Hk3.eigSum_mul_proj_eq h e Ec lab he hs hl
  obtain ⟨a, b, -⟩ := GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup s (fun i => h i * e)
  refine ⟨a hc, fun Q hQ => ?_⟩
  have h0 : (fun i => cj s ((0 : I → ℂ) i)) = 0 := by funext i; simp
  rw [b Q, hq _ (by rw [h0]; exact hQ)]

theorem cxSys_cj_iff {K I : Type} [Field K] {σ τ : K →+* ℂ} {s : Bool} (h : ∀ a, σ a = cj s (τ a)) (H : (I → K) → Prop) (y : I → ℂ) :
    cxSys σ H (fun i => cj s (y i)) ↔ cxSys τ H y := by
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun e i
    simp only [h] at this
    simpa [cj_cj] using congrArg (cj s) this
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, funext fun i => (h _).symm⟩

set_option maxHeartbeats 2000000 in
theorem heckeTheta_level3_exists_alt : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  intro hHowe hHC hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hParts hTS hPin
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hCoreE, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreE hEx
  have hSch : SchurAll R.toRealDat :=
    ⟨fun _ _ _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      fun _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2⟩
  have hTr := (hPin (GlobalTheory.T.exists_separating_inert_eigenvalue_passage hHowe R F hLI hC hEx hSch hJ hirr hB hPos)).1
  have hOps := fun i => GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hirr R.SF hSF i
  choose h hIsW hNorm hGc hSup hInv hEig hChar using hOps
  have hDict := GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner hHowe R F hLI hC hEx hSch hJ
  choose pl cV cW hD using hDict
  have hLaws := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hirr
  have hcut := fun j => tw_cut_eig (twAt D.what₂.embLL A3.A.v0) (fun i => h j (pl j A3.A.μ0 i) (cW j A3.A.μ0 i)) (eH R.toRealDat j)
    (Wcc R.toRealDat R.SF j) (fun c => labW j (pl j A3.A.μ0) (cW j A3.A.μ0) c) (hLaws j).1 (hSup j)
    (fun c w hw i => hEig j c _ ((hD j A3.A.μ0).good i) _ w hw)
  refine ⟨fun j t i => Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j), ?_, ?_, ?_⟩
  · intro j t i u
    obtain ⟨hV, hVo, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j t
    have hK := RealDat3.kFormL_of (R := R) (F := F) hCore.models
    have hop : (R.toCx3 F).opLC j t (Sum.inl i) = Tw.map (E := (R.HV j t).H) (F := (R.HV j t).H) (twAt D.what₂.embLL A3.A.v0) (hV (pl j t i) (cV j t i)) := by
      refine LinearMap.ext_on_range (hK j t).2 fun k => ?_
      rw [← CxData.jL_opL _ hK]
      show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j t ((A3.liftI j t).opAll i _)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (hV _ _ (R.jV j t _))
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hD j t).op hV hVo i _)
    have hs := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hCore hSch hirr R.SF hSF j t (pl j t i) ((hD j t).good i) _ _ ((hD j t).mat i) hV hVo).1 (h j) (hIsW j)
    rw [hop]
    show R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) =
      Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j)
        (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u)))
    rw [map_smul]
    congr 1
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) (eH R.toRealDat j (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))))
    rw [(hLaws j).2.2.2 t, hs]
  · intro j
    exact (hcut j).1
  · intro j p
    have hv := fun a => R.toRealDat.emb0 a
    have hQ0 : ¬ cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
      intro h0
      have h1 : (0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) = fun i => cj (twAt D.what₂.embLL A3.A.v0) ((0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) i) := by
        funext i; simp
      rw [h1] at h0
      exact GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType R F hC j p ((cxSys_cj_iff hv _ _).1 h0)
    have key := (hcut j).2 _ hQ0
    show Tw.sub _ (R.Wp3 j p) = _
    refine Eq.trans ?_ key.symm
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      by_cases hne : R.Wc' j c = ⊥
      · rw [hne]; exact bot_le
      · exact le_iSup₂_of_le c ((cxSys_cj_iff hv _ _).2
          (GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr j _ _ _ (hD j A3.A.μ0) p c hc hne)) (hWc j c).le
    · refine iSup₂_le fun c hc => ?_
      rw [← hWc j c]
      exact GlobalTheory.T.eigenPart_le_typePart_of_passage hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr hParts hTS j _ _ _ (hD j A3.A.μ0) p c
        ((cxSys_cj_iff hv _ _).1 hc)

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstOfCoordRev
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.SstModel

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_of_coord_rev [Nonempty ι] (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ') :
    IsSst P ρ := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [GlobalTheory.AboveL.RepConj.isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, GlobalTheory.AboveL.RepConj.finrank_pi_card,
    GlobalTheory.AboveL.RepConj.finrank_pi_card, mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos h

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_of_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1)
    (h : IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :
    IsSst P (Bw.repE L₁ r₁) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord_rev P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSst_of_isModel {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {r : ↥Gw →* GL (Fin m) (Om l)}
    {L : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥L.1} (hm : IsModel Bw r L r') (hs : IsSstAt P Bw r) :
    IsSst P (Bw.repE L r') := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := hs
  have l₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have l₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e := IsModel.unique Bw r (h₁.enlarge l₁) (hm.enlarge l₂)
  have h3 := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hp
  rw [e] at h3
  exact isSst_of_enlarge P Bw l₂ r' h3

end GlobalTheory.SstModel

namespace GlobalTheory.SstModel

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1), IsModel Bw r LL' r' → IsSstAt P Bw r → IsSst P (Bw.repE LL' r') := by
  intro l _ P AI _ E Ω _ _ _ Gw O _ _ _ Bw a r LL' r' hm hs
  exact isSst_of_isModel P hm hs

end GlobalTheory.SstModel

end
end

