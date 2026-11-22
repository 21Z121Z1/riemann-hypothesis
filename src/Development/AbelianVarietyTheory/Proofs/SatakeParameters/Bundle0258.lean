import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsCompletionAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MonodromyZeroIffRestricts
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotient
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.DecCover

theorem main : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  intro Ω _ F _ _ _ _ v N hN
  classical
  have : IsGalois F Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN N.one_mem
  have hcheb := fun g : G F Ω =>
    GlobalTheory.Published.cheb_holds F Ω U.toSubgroup U.isOpen U.isNormal' g {v}
  choose u hu _ _ B hB _ σ hσ hσU using hcheb
  have hmem : ∀ g : G F Ω, (σ g)⁻¹ * g ∈ N := by
    intro g
    apply hU
    have h1 := U.isNormal'.conj_mem _ (hσU g) (σ g)⁻¹
    have h2 : (σ g)⁻¹ * (σ g * g⁻¹) * (σ g)⁻¹⁻¹ = ((σ g)⁻¹ * g)⁻¹ := by group
    rw [h2] at h1
    have h3 := U.toSubgroup.inv_mem h1
    rw [inv_inv] at h3
    exact h3
  have hopen : ∀ g : G F Ω, IsOpen {h : G F Ω | (σ g)⁻¹ * h ∈ N} := fun g =>
    hN.preimage (continuous_mul_left _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G F Ω => {h : G F Ω | (σ g)⁻¹ * h ∈ N}) hopen
    (fun g _ => Set.mem_iUnion.2 ⟨g, hmem g⟩)
  refine ⟨t.image u, ?_, fun g => ?_⟩
  · intro hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    exact hu i (by simp [hi])
  · obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    refine ⟨u i, Finset.mem_image_of_mem u hi, B i, hB i, σ i, (hσ i).1, (σ i)⁻¹ * g, hgi, ?_⟩
    group

end GlobalTheory.DecCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.RepConj

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

theorem finrank_pi_card {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
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
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_pi_card, finrank_pi_card, h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

end GlobalTheory.AboveL.RepConj

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.RepConj

end GlobalTheory.AboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodGenericSer

open GlobalTheory.GoodGenericInv

theorem goodGenericCharacter_of_seriesTypes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC s hOk hser
  have hG := hC.base.grp
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hprod : ∀ χ ∈ A3.A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) :=
    GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hG.record hser (fun χ hχ => hOk2.irr χ hχ)
  letI : Fintype F.P0 := Fintype.ofFinite _
  have hsum : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    fun χ hχ => by
      letI : Fintype F.lv2.P0 := (inferInstance : Fintype F.P0)
      exact GlobalTheory.RealOneVector.typeSum_base_eq_card D G Pl0 T A3.A Ks R.toRealDat F.lv2 hG.levels hprod χ hχ
  have hone : ∀ χ ∈ A3.A.X, χ 1 ≠ 0 := fun χ hχ h =>
    GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero
      (GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hOk2.irr χ hχ)) (by rw [h, map_zero])
  have hcard : (Fintype.card F.P0 : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun χ hχ => GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) (by rw [hsum χ hχ]; exact hcard),
    fun χ hχ => ?_⟩
  obtain ⟨ψ', -, hlev, -⟩ := hG.levels
  have hcls : ∀ g h, χ (g * h * g⁻¹) = χ h := by
    obtain ⟨n, ρ, -, hρ⟩ := hOk2.irr χ hχ
    intro g h
    apply (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)).injective
    rw [← hρ, ← hρ, ρ.char_conj]
  have hmem : ∀ x : G0 R.Pg D.R.r, R.eG.symm x ∈ F.P0 →
      R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) ∈ F.P0 := by
    intro x hx
    have h1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hx)
    have h2 := alternatingSignDiagonal_conj_mem_genericLevel ψ' h1
    have h3 : _ ∈ (R.toRealDat.levR F.lv2 false).H := (congrArg LevelP.H hlev).symm ▸ h2
    exact h3
  let t : G := R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r)
  have he : ∀ x, t * R.eG.symm x * t⁻¹ = R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) := by
    intro x; simp only [t, map_mul, map_inv]
  have ht : ∀ h ∈ F.P0, t * h * t⁻¹ ∈ F.P0 := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    rw [he]; exact hmem x hh
  have hψ : ∀ (h : G) (hh : h ∈ F.P0), F.ψ0 ⟨t * h * t⁻¹, ht h hh⟩ = (F.ψ0 ⟨h, hh⟩)⁻¹ := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    have hs : (⟨t * R.eG.symm x * t⁻¹, ht _ hh⟩ : F.P0) = ⟨_, hmem x hh⟩ := Subtype.ext (he x)
    rw [hs]
    apply Units.ext
    apply D.what₂.embLL.injective
    have hx1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hh)
    have k1 : Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩) =
        (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ :=
      calc Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩)
          = (R.toRealDat.levR F.lv2 false).chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, hmem x hh⟩ := rfl
        _ = (P0 R.Pg D.R.r ψ').chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ' hx1⟩ :=
            level_character_eq_of_eq hlev _ _ _
        _ = ((P0 R.Pg D.R.r ψ').chi ⟨x, hx1⟩)⁻¹ := genericLevelCharacter_alternatingSign_conj_inv ψ' hx1
        _ = ((R.toRealDat.levR F.lv2 false).chi ⟨x, hh⟩)⁻¹ := by rw [level_character_eq_of_eq hlev x hh hx1]
        _ = (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ := rfl
    have k3 := congrArg Units.val k1
    simpa [Units.coe_map, Units.val_inv_eq_inv_val, map_inv₀] using k3
  refine GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) ?_
  rw [typeSum_inv_eq F.P0 F.ψ0 χ hcls t ht hψ, hsum χ hχ]
  exact hcard

end GlobalTheory.GoodGenericSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescent
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RealNormChar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp

open scoped GroundTheory.Global.AdeleBaseChange in
open GlobalTheory.UnitaryHeckeBaseChange in

theorem ideleNorm_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.GalOfCusp.ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      exact mul_comm _ _
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  intro K M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield K) (maximalRealSubfield M) := (realHom K M).toAlgebra
  haveI : IsScalarTower (maximalRealSubfield K) (maximalRealSubfield M) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (maximalRealSubfield K) K M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨normChar (maximalRealSubfield M) χ,
    fun u => (normChar_locInf χ u (IsTotallyReal.isReal u)).trans (hsign _), fun x => ?_⟩
  show χ.1 (GroundTheory.Global.ideleNorm _ _ (GlobalTheory.GalOfCusp.ideleNorm M x)) =
    χ.1 (GlobalTheory.GalOfCusp.ideleNorm K (GroundTheory.Global.ideleNorm K M x))
  rw [ideleNorm_eq, ideleNorm_eq, GroundTheory.Global.ideleNorm_ideleNorm, GroundTheory.Global.ideleNorm_ideleNorm]

end GlobalTheory.RealNormChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFullSetCompEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

namespace GlobalTheory.LevDict

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.DrinLev.HT GlobalTheory.UPel.HT.WPart

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow}
  {i₀ : Fin D.a} {πw : WProj D b i₀} {N : ℕ} {T : Type} [CommRing T] [Algebra Ow T]
  {o : Obj b N (spMap (algebraMap Ow T))} {H : VarpiDivModule p Ow T}

def ptImg (wp : WPart πw o H) {k : ℕ} (h : H.G.A k →ₐ[T] T) : Sp T ⟶ o.A.left :=
  spMap ((h.comp (wp.iH.app k : wp.G.A k →ₐ[T] H.G.A k)).toRingHom) ≫ (wp.t.y k).left

end GlobalTheory.LevDict

namespace GlobalTheory.LevDict

open GlobalTheory.UPel.HT GlobalTheory.DrinLev.HT

theorem isFullSet_comp_equiv {S : Scheme.{0}} {Z : Over S} {J J' : Type} {P : J → (𝟙_ (Over S) ⟶ Z)}
    (h : GlobalTheory.DrinLev.IsFullSet Z P) (e : J' ≃ J) : GlobalTheory.DrinLev.IsFullSet Z (P ∘ e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(Equiv.finite_iff e).2 h1, ?_, fun c f => ?_⟩
  · rw [Nat.card_congr e]; exact h2
  · rw [h3 c f]
    exact (finprod_comp_equiv e (f := fun i => c.ev (P i) f)).symm

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

def htLevelAct {o : Obj b N s} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} (L : HTLevel o w m e)
    (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : HTLevel o w m e where
  α x := L.α (g.val.mulVec x)
  map_add x y := by rw [Matrix.mulVec_add]; exact L.map_add _ _
  map_smul c x := by rw [Matrix.mulVec_smul]; exact L.map_smul _ _
  full := by
    obtain ⟨G, β, hβ, hf⟩ := L.full
    exact ⟨G, fun x => β (GlobalTheory.VDiv.glEquiv g x), fun x => hβ (GlobalTheory.VDiv.glEquiv g x), isFullSet_comp_equiv hf (GlobalTheory.VDiv.glEquiv g).toEquiv⟩

@[simp] theorem htLevelAct_α {o : Obj b N s} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} (L : HTLevel o w m e)
    (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) (x : Fin D.n → 𝓞 D.F ⧸ w ^ m) :
    (htLevelAct L g).α x = L.α (g.val.mulVec x) := rfl

end GlobalTheory.LevDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem eig_pow_of_rep {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) (σ : Weil h) (k : ℕ) :
    x.eig (σ ^ k) = (x.eig σ).map (· ^ k) := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.eig_mk, WD.eig_mk, map_pow]
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n k
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (a.ρ σ))
  rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
  exact h2

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

open Pointwise

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastEqZeroOfDvdCard
section
namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCoreLeFixingSubgroupNormalClosure
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.NormalClosureSolv

open Pointwise

variable {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]

theorem algebraMap_mem_smul_iff (γ : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (c : F) :
    algebraMap F Ω c ∈ γ • A ↔ algebraMap F Ω c ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

theorem isPlaceOver_smul' [NumberField F] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (γ : Ω ≃ₐ[F] Ω) : IsPlaceOver (γ • A) v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, algebraMap_mem_smul_iff,
    algebraMap_mem_smul_iff, map_inv₀]

end GlobalTheory.NormalClosureSolv
end

