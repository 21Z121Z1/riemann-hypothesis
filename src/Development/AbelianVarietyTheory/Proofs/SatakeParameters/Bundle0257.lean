import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjectiveOfFg
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

private theorem coe_le_one {L Ω : Type} [Field Ω] [Field L] [NumberField L] [Algebra L Ω]
    (A : ValuationSubring Ω) (c : 𝓞 L) : A.valuation (algebraMap L Ω (c : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))

theorem exists_isPlaceOver_of_tower : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h
  let m : Ideal (𝓞 L) :=
    { carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }
  have hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1 := fun y => Iff.rfl
  have hprime : m.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]; simp
    · intro x y hxy
      rw [hmem, hmem] at *
      have e : ((x * y : 𝓞 L) : L) = (x : L) * y := rfl
      rw [e, map_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      exact absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))
  have hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hmem, ← h x]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      have e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
      rw [e, ← IsScalarTower.algebraMap_apply]
    rw [this]
  have hne : m ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m := (hK x).mpr hx
    rw [hb, Ideal.mem_bot] at h1
    apply hx0
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])
  refine ⟨⟨m, hprime, hne⟩, ?_, ?_⟩
  · intro y
    exact (hmem y).symm.trans Iff.rfl
  · apply HeightOneSpectrum.ext
    ext x
    exact hK x

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.OpenNormal

theorem exists_open_normal_le : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → ∃ N : Subgroup (G F Ω), N.Normal ∧ IsOpen (N : Set (G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  intro Ω _ F _ _ _ _ U hU
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (G F Ω) := inferInstanceAs (CompactSpace Gal(Ω/F))
  haveI : Finite (G F Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨U.normalCore, U.normalCore_normal, ?_, inferInstance, U.normalCore_le⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))

end GlobalTheory.OpenNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTriv
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField
open scoped Matrix

namespace GlobalTheory.RepEqAt

section General

open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_triv (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) {n : ℕ} (hn : 0 < n)
    (Λ : GenLat E N) (hU : Λ.Unimod) :
    ∃ γ : Matrix (Fin N) (Fin N) E, IsUnitaryM γ ∧ ∃ k : ℕ, Nat.Coprime k n ∧
      (∀ v ∈ Λ.La, k • (γ *ᵥ v) ∈ Formalism.L2.Pj.stdLat E N) ∧
      ∀ x ∈ Formalism.L2.Pj.stdLat E N, ∃ v ∈ Λ.La, γ *ᵥ v = k • x := by
  have hsub : ∀ a b : 𝓞 E ⧸ Ideal.span {((1 : ℕ) : 𝓞 E)}, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a - b, by simp⟩)
  have hiso : IsIsomMod Λ 1 0 := by
    refine ⟨fun y => ⟨0, funext fun j => hsub _ _⟩, fun v => ⟨fun _ => ⟨v, v.2, by simp⟩, fun _ => rfl⟩,
      fun v w x y _ _ => ?_⟩
    obtain ⟨a, ha⟩ := (hU w).1 w.2 v v.2
    refine ⟨a - ∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j), ?_⟩
    have e1 : ∑ j, (v : Fin N → E) j * IsCMField.complexConj E ((w : Fin N → E) j) = (a : E) := by
      refine Eq.trans ?_ ha.symm
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) =
        ((∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j) : 𝓞 E) : E) := by
      change _ = algebraMap (𝓞 E) E _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
    rw [e1, e2, Nat.cast_one, one_mul]
    exact (map_sub (algebraMap (𝓞 E) E) _ _).symm
  obtain ⟨γ, hγ, ⟨k, hk, h1, h2⟩, -⟩ :=
    GlobalTheory.RepTrivial.repExists E N hur 1 n one_pos hn Λ 0 hU hiso
  rw [GlobalTheory.GenusLatCompare.span_smul_le_iff] at h1 h2
  exact ⟨γ, hγ, k, hk, fun v hv => h1 _ ⟨v, hv, rfl⟩, fun x hx => h2 x hx⟩

end General

theorem repExS (D : D7) : GL3Theta.repExS D := by
  letI := D.host.cmStar
  intro n hn N L L₀
  have hur := Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  have hst : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hU : ∀ M : SDLat D.host.E N, (⟨M.1⟩ : Formalism.L2.Pj.GenLat D.host.E N).Unimod := fun M v => by
    refine (M.2.2.2 v).trans (forall₂_congr fun w _ => ?_)
    have e : ∀ x y : Fin N → D.host.E, IsCMField.complexConj D.host.E (stdH D.host.E N x y) =
        stdH D.host.E N y x := fun x y => by
      rw [← hst]
      simp [stdH, mul_comm]
    have c : ∀ x y : Fin N → D.host.E, stdH D.host.E N x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range →
        stdH D.host.E N y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      rintro x y ⟨a, ha⟩
      refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E a, ?_⟩
      rw [← e, ← ha]
      exact IsCMField.coe_ringOfIntegersComplexConj D.host.E a
    exact ⟨c w v, c v w⟩
  have hun : ∀ γ : Matrix (Fin N) (Fin N) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ →
      γ ∈ Matrix.unitaryGroup (Fin N) D.host.E := fun γ h => Matrix.mem_unitaryGroup_iff'.2 h
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := exists_triv hur hn _ (hU L)
  obtain ⟨δ, hδ, l, hl, h3, h4⟩ := exists_triv hur hn _ (hU L₀)
  have hδ1 : star δ * δ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun δ hδ)
  have hγ1 : star γ * γ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun γ hγ)
  have hinv : ∀ v, star δ *ᵥ (δ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hδ1, Matrix.one_mulVec]
  refine ⟨⟨star δ * γ, mul_mem (Unitary.star_mem (hun δ hδ)) (hun γ hγ)⟩, k * l,
    Nat.Coprime.mul_left hk hl, ?_, fun x hx => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, e⟩ := h4 _ (h1 v hv)
    have : ((k * l : ℕ) : D.host.E) • ((star δ * γ) *ᵥ v) = u := by
      rw [← hinv u, e, Nat.cast_smul_eq_nsmul, ← Matrix.mulVec_mulVec, smul_smul, mul_comm l k,
        Matrix.mulVec_smul]
    exact this ▸ hu
  · obtain ⟨u, hu, e⟩ := h2 _ (h3 x hx)
    refine ⟨u, hu, ?_⟩
    change (star δ * γ) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, e, smul_smul, Matrix.mulVec_smul, hinv, Nat.cast_smul_eq_nsmul]

end GlobalTheory.RepEqAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitComp

theorem exists_comp_and_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ a U hU w hw
  let π : GlobalTheory.DefU.AutSub E a := ⟨U, hU⟩
  refine ⟨?_, fun σ σ' hσ hσ' => ?_⟩
  · obtain ⟨σ, -, h, -⟩ := GlobalTheory.DefU.exists_locComp_split E a π w hw
    exact ⟨σ, h⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E a w hw
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E a w
    set p : locU a w →* GL (Fin a) (w.adicCompletion E) := (cLoc w).comp (locU a w).subtype with hpdef
    have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
    have hsurj : ∀ g, p (e.symm g) = g := fun g => by
      rw [hp]; exact e.apply_symm_apply g
    have hirr : ∀ τ : SmIrr (GL (Fin a) (w.adicCompletion E)), Representation.IsIrreducible (τ.ρ.comp p) := fun τ => by
      rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv τ.ρ e.toMulEquiv τ.irred
    have hmap : ∀ τ : SmIrr (GL (Fin a) (w.adicCompletion E)),
        IsCompAlong U (locU a w) p τ.ρ → ∃ F : Representation.IntertwiningMap (τ.ρ.comp p) (π.rep.comp (locU a w).subtype), F ≠ 0 := by
      rintro τ ⟨-, f, hf0, hfm, hf⟩
      refine ⟨⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩, fun h => hf0 ?_⟩
      exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v)
    obtain ⟨F, hF⟩ := hmap σ hσ
    obtain ⟨F', hF'⟩ := hmap σ' hσ'
    obtain ⟨T⟩ := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E a) (locU a w) π.V σ.V σ'.V π.rep (locU a w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p) π.isIrreducible_rep (hirr σ) (hirr σ')
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF).2 F' hF'
    refine ⟨Representation.Equiv.mk' ⟨T.toLinearEquiv.toLinearMap, fun g => ?_⟩ T.toLinearEquiv.invFun
      T.toLinearEquiv.left_inv T.toLinearEquiv.right_inv⟩
    have := T.isIntertwining' (e.symm g)
    rw [← hsurj g]
    exact this

end GlobalTheory.SplitComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.FixProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem rU_mul (x y : UA E a) (f : UA E a → ℂ) : RU E a (x * y) f = RU E a x (RU E a y f) := by
  rw [map_mul]; rfl

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU a w ≤ finU E a :=
  fun _ hx => (Subgroup.mem_inf.1 hx).1

theorem commute_of_apart {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) {x y : UA E a}
    (hx : x ∈ locU a w) (hy : y ∈ locU a u) : Commute x y := by
  show x * y = y * x
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hx, GlobalTheory.DefU.LocRet.mem_locU_inf hy]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have hv' : v.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E)) := hv ▸ h
      simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hy hv', one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hx hv, one_mul, mul_one]

section Avg

variable (K : Subgroup (UA E a)) (K' : Subgroup K) [Fintype (K ⧸ K')]

def avg : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ) :=
  ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a)

theorem avg_apply (f : UA E a → ℂ) :
    avg K K' f = ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a) f := by
  unfold avg
  exact LinearMap.sum_apply _ _ _

theorem avg_comm {c : UA E a} (hc : ∀ k ∈ K, Commute c k) (f : UA E a → ℂ) :
    avg K K' (RU E a c f) = RU E a c (avg K K' f) := by
  rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← rU_mul, ← rU_mul, (hc _ (Quotient.out q).2).eq]

theorem avg_of_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K, RU E a k f = f) :
    avg K K' f = (Fintype.card (K ⧸ K') : ℂ) • f := by
  rw [avg_apply, Finset.sum_congr rfl (fun q _ => hf _ (Quotient.out q).2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem avg_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K', RU E a ((k : K) : UA E a) f = f) (k : UA E a) (hk : k ∈ K) :
    RU E a k (avg K K' f) = avg K K' f := by
  rw [avg_apply, map_sum]
  have key : ∀ q : K ⧸ K', RU E a k (RU E a ((Quotient.out q : K) : UA E a) f) =
      RU E a ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : UA E a) f := by
    intro q
    have hm : (Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (⟨k, hk⟩ : K) * Quotient.out q = Quotient.out ((⟨k, hk⟩ : K) • q) *
        ((Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q)) := (mul_inv_cancel_left _ _).symm
    have e' := congrArg (fun z : K => (z : UA E a)) e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at e'
    have hm' := hf _ hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hm'
    rw [← rU_mul, e', rU_mul, hm']
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun q => rfl)

end Avg

theorem mend (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (UA E a)) (hKw : K ≤ locU a w) (hKc : IsCompact (K : Set (UA E a)))
    {φw : UA E a → ℂ} (hφwU : φw ∈ U) (hφw0 : φw ≠ 0) (hφwK : ∀ k ∈ K, RU E a k φw = φw)
    {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0) :
    ∃ ψ ∈ U, ψ ≠ 0 ∧ (∀ k ∈ K, RU E a k ψ = ψ) ∧
      ∀ y : UA E a, (∀ x ∈ locU a w, Commute y x) → RU E a y φ = φ → RU E a y ψ = ψ := by
  classical

  let S := Submodule.span ℂ (Set.range fun g : UA E a => RU E a g φ)
  have hSU : S ≤ U := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hU.stable g φ hφU)
  have hSst : ∀ x, ∀ f ∈ S, RU E a x f ∈ S := by
    intro x f hf
    have : S ≤ S.comap (RU E a x) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU E a x (RU E a g φ) ∈ S
      rw [← rU_mul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact this hf
  have hφS : φ ∈ S := by
    have h1 : RU E a 1 φ = φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = U := by
    rcases hU.irred S hSU hSst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hφS)) hφ0
    · exact h
  have hφwS : φw ∈ S := hSeq ▸ hφwU
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφwS

  let r : UA E a → UA E a := fun g => (GlobalTheory.DefU.LocRet.ret w a g : UA E a)
  have hr : ∀ g, r g ∈ locU a w := fun g => (GlobalTheory.DefU.LocRet.ret w a g).2
  have hd : ∀ g, ∀ x ∈ locU a w, Commute ((r g)⁻¹ * g) x := fun g x hx =>
    GlobalTheory.DefU.LocRet.commute_ret g ⟨x, hx⟩
  have hsplit : ∀ g, RU E a g φ = RU E a ((r g)⁻¹ * g) (RU E a (r g) φ) := by
    intro g
    rw [← rU_mul, (hd g (r g) (hr g)).eq, mul_inv_cancel_left]

  have hKf : K ≤ finU E a := hKw.trans (locU_le_finU w)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let K' : Subgroup K :=
    { carrier := {k | ∀ g ∈ c.support, RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ}
      mul_mem' := fun {x y} hx hy g hg => by
        show RU E a ((x : UA E a) * (y : UA E a)) _ = _
        rw [rU_mul, hy g hg, hx g hg]
      one_mem' := fun g _ => by
        show RU E a 1 _ = _
        rw [map_one]; rfl
      inv_mem' := fun {x} hx g hg => by
        have h := hx g hg
        show RU E a ((x : UA E a)⁻¹) _ = _
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) (RU E a (r g) φ)) := by rw [h]
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hK'o : IsOpen (K' : Set K) := by
    have e : (K' : Set K) =
        ⋂ g ∈ c.support, {k : K | RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ} := by
      ext k
      rw [Set.mem_iInter₂]
      rfl
    rw [e]
    refine isOpen_biInter_finset fun g _ => ?_
    have ho := (hU.aut _ (hU.stable (r g) φ hφU)).level
    have hcont : Continuous fun k : K => (⟨(k : UA E a), hKf k.2⟩ : finU E a) :=
      continuous_subtype_val.subtype_mk _
    exact ho.preimage hcont
  haveI : Finite (K ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'o
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  have hA : avg K K' φw = c.sum fun g b => b • RU E a ((r g)⁻¹ * g) (avg K K' (RU E a (r g) φ)) := by
    rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hsplit g, avg_comm K K' (fun k hk => hd g k (hKw hk))]
  by_cases h0 : ∀ g ∈ c.support, avg K K' (RU E a (r g) φ) = 0
  · exfalso
    have hz : avg K K' φw = 0 := by
      rw [hA, Finsupp.sum]
      exact Finset.sum_eq_zero fun g hg => by rw [h0 g hg, map_zero, smul_zero]
    rw [avg_of_fixed K K' hφwK] at hz
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    exact hφw0 ((smul_eq_zero.1 hz).resolve_left hcard)
  · push_neg at h0
    obtain ⟨g, hg, hne⟩ := h0
    refine ⟨avg K K' (RU E a (r g) φ), ?_, hne, ?_, ?_⟩
    · rw [avg_apply]
      exact Submodule.sum_mem _ fun q _ => hU.stable _ _ (hU.stable _ _ hφU)
    · exact avg_fixed K K' (fun k hk => hk g hg)
    · intro y hy hyφ
      rw [← avg_comm K K' (fun k hk => hy k (hKw hk)), ← rU_mul, (hy (r g) (hr g)).eq, rU_mul, hyφ]

theorem fix_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w a) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  intro E _ _ _ a U hU w₀ K hKl hKeq hKc hKint _ hφ'
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU E a) :=
    { carrier := {k | RU E a (k : UA E a) φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        show RU E a ((x : UA E a) * (y : UA E a)) φ₀ = φ₀
        rw [rU_mul]
        exact (congrArg _ hy).trans hx
      one_mem' := by
        show RU E a 1 φ₀ = φ₀
        rw [map_one]; rfl
      inv_mem' := fun {x} hx => by
        show RU E a ((x : UA E a)⁻¹) φ₀ = φ₀
        have hx' : RU E a (x : UA E a) φ₀ = φ₀ := hx
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) φ₀) := by rw [hx']
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hLo : IsOpen (L : Set (finU E a)) := (hU.aut φ₀ hφ₀U).level
  have hev := GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo
  have hgood : ∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, RU E a x φ₀ = φ₀ := by
    filter_upwards [hev, hKint] with w h1 h2 x hx
    exact h1 x (hKl w hx) (h2 x hx) (locU_le_finU w (hKl w hx))
  have hB := Filter.eventually_cofinite.1 hgood
  have main : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), ∃ φ ∈ U, φ ≠ 0 ∧ ∀ u, Apart u w₀ →
      ((∀ x ∈ K u, RU E a x φ₀ = φ₀) ∨ u ∈ S) → ∀ x ∈ K u, RU E a x φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨φ₀, hφ₀U, hφ₀, fun u _ hu x hx => ?_⟩
      rcases hu with hu | hu
      · exact hu x hx
      · exact absurd hu (Finset.notMem_empty u)
    | insert w S hwS ih =>
      obtain ⟨φ, hφU, hφ0, hφ⟩ := ih
      by_cases hw : Apart w w₀
      · obtain ⟨φw, hφwU, hφw0, hφwK⟩ := hφ' w hw
        obtain ⟨ψ, hψU, hψ0, hψK, hψy⟩ := mend U hU w (K w) (hKl w) (hKc w) hφwU hφw0 hφwK hφU hφ0
        refine ⟨ψ, hψU, hψ0, fun u hu hu' x hx => ?_⟩
        by_cases hap : Apart u w
        · refine hψy x (fun z hz => commute_of_apart hap (hKl u hx) hz) ?_
          rcases hu' with h | h
          · exact hφ u hu (Or.inl h) x hx
          · rcases Finset.mem_insert.1 h with rfl | h
            · exact absurd rfl hap
            · exact hφ u hu (Or.inr h) x hx
        · rw [hKeq u w hap] at hx
          exact hψK x hx
      · refine ⟨φ, hφU, hφ0, fun u hu hu' x hx => ?_⟩
        rcases hu' with h | h
        · exact hφ u hu (Or.inl h) x hx
        · rcases Finset.mem_insert.1 h with rfl | h
          · exact absurd hu hw
          · exact hφ u hu (Or.inr h) x hx
  obtain ⟨φ, hφU, hφ0, hφ⟩ := main hB.toFinset
  refine ⟨φ, hφU, hφ0, fun u hu x hx => hφ u hu ?_ x hx⟩
  by_cases h : ∀ x ∈ K u, RU E a x φ₀ = φ₀
  · exact Or.inl h
  · exact Or.inr (hB.mem_toFinset.2 h)

end GlobalTheory.Cong.FixProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition
section
namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimesStatement
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.TopXiInvQ.xiTop_invQ | exact GlobalTheory.TopXiInvQ.xiTop_invQ | (intros; apply GlobalTheory.TopXiInvQ.xiTop_invQ <;> assumption)
end

