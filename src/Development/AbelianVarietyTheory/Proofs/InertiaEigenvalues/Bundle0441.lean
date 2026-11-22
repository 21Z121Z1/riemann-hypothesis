import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeSame
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem SameField.basic {D D' : D7} (h : SameField D D') (h1 : SameGalois D.nd D'.nd) (h2 : TwistDataAgreeAcrossCoefficients D.ntw D'.ntw) :
    D.what₂.places.Pl = D'.what₂.places.Pl ∧ (IsGalois ℚ ↥D.LL0 → IsGalois ℚ ↥D'.LL0) ∧
    (∃ φ : ↥D.LL0 ≃+* ↥D'.LL0, ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ b x,
      HEq (sideEmb i b x) (sideEmb i' b (φ x))) ∧
    (∀ (ψ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
      (ψ' : D'.what₂.places.Pl → (G D'.host.E D'.nd.Om →* (D'.what₂.LL)ˣ)), HEq ψ ψ' →
      ((∀ w, ψ (D.what₂.places.conj w) = ψ w) → ∀ w, ψ' (D'.what₂.places.conj w) = ψ' w) ∧
      ∀ w w', HEq w w' → HEq (ψ w) (ψ' w') ∧ (ψ w = 1 → ψ' w' = 1)) ∧
    ∀ (w : D.what₂.places.Pl) (w' : D'.what₂.places.Pl), HEq w w' →
      HEq (D.what₂.places.conj w) (D'.what₂.places.conj w') ∧
      (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ b, ReadsAt i b w ↔ ReadsAt i' b w') ∧
      ∀ (p : TwPack D) (p' : TwPack D'), HEq p p' → ∀ (b : Bool) (ψ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
        (ψ' : G D'.host.E D'.nd.Om →* (D'.what₂.LL)ˣ), HEq ψ ψ' →
        (∃ ρ : Reading p.1 p.2.2.1 b w, ∀ g, ρ.emb ((ψ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
          (algebraMap (D.ntw.Ok p.1 p.2.2.1) ρ.Oe
            ((BlochKatoReduction.Gen.psiAt b p.2.2.2 (D.ntw.art p.1 p.2.1 g) : (D.ntw.Ok p.1 p.2.2.1)ˣ) : D.ntw.Ok p.1 p.2.2.1))) →
        ∃ ρ : Reading p'.1 p'.2.2.1 b w', ∀ g, ρ.emb ((ψ' g : (D'.what₂.LL)ˣ) : D'.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
          (algebraMap (D'.ntw.Ok p'.1 p'.2.2.1) ρ.Oe
            ((BlochKatoReduction.Gen.psiAt b p'.2.2.2 (D'.ntw.art p'.1 p'.2.1 g) : (D'.ntw.Ok p'.1 p'.2.2.1)ˣ) : D'.ntw.Ok p'.1 p'.2.2.1)) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := h
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D
  cases ‹Rows.Data _›
  cases ‹NData _ _ _›
  cases ‹NTw _ _ _ _ _›
  cases D'
  cases ‹Rows.Data _›
  cases ‹NData _ _ _›
  cases ‹NTw _ _ _ _ _›
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 b6 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst a1; subst a2; subst a3; subst b1; subst b2; subst b3; subst b4
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst b5; subst b6
  refine ⟨rfl, id, ⟨RingEquiv.refl _, fun i i' hi b x => ?_⟩, fun ψ ψ' hψ => ?_, fun w w' hw => ?_⟩
  · subst hi
    exact HEq.rfl
  · subst hψ
    refine ⟨id, fun w w' hw => ?_⟩
    subst hw
    exact ⟨HEq.rfl, id⟩
  · subst hw
    refine ⟨HEq.rfl, fun i i' hi b => ?_, fun p p' hp b ψ ψ' hψ => ?_⟩
    · subst hi
      exact Iff.rfl
    · subst hp
      subst hψ
      rintro ⟨ρ, hρ⟩
      exact ⟨@Reading.mk _ _ _ _ _ ρ.Oe ρ.cr ρ.dom ρ.dvr ρ.alg ρ.inj ρ.fin ρ.loc ρ.emb ρ.emb_w ρ.emb_side, hρ⟩

end GlobalTheory.TwistChoice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.CutFam

theorem exists_of_mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X)
    {c : O} (hc : c ∈ ccAt T Z π) : ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = c := by
  unfold ccAt Ideal.map at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨f, hf, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, add_mem hf hg, rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨algebraMap O T r * f, Ideal.mul_mem_left _ _ hf, ?_⟩
    simp [smul_eq_mul]

theorem mem_ccIdeal_iff {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (f : T) :
    f ∈ ccIdeal T Z ↔ ∀ y, y ∉ Z → (f : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa using this
  · intro h
    funext y
    simpa using h y.1 y.2

theorem exists_ne_zero {O X : Type} [CommRing O] [IsDomain O] [Fintype X] (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X) (hπ : π ∈ Z) :
    ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π ≠ 0 := by
  classical
  have h : ∀ x : {x // x ∉ Z}, ∃ f : T, (f : X → O) x.1 ≠ (f : X → O) π := by
    intro x
    obtain ⟨f, hfT, hf⟩ := hsep x.1 π (fun h => x.2 (h ▸ hπ))
    exact ⟨⟨f, hfT⟩, hf⟩
  choose g hg using h
  refine ⟨∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)), ?_, ?_⟩
  · rw [mem_ccIdeal_iff]
    intro y hy
    rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) ?_
    simp
  · rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun x _ => ?_
    have e : ∀ c : O, ((algebraMap O T c : T) : X → O) π = c := fun c => by simp
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, e]
    exact sub_ne_zero.mpr (hg x).symm

theorem length_span {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) = IsDiscreteValuationRing.addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem lenUnit_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) {a b : O}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    lenUnit (O := O) l (O ⧸ Ideal.span {a * b}) =
      lenUnit (O := O) l (O ⧸ Ideal.span {a}) + lenUnit (O := O) l (O ⧸ Ideal.span {b}) := by
  unfold lenUnit
  rw [length_span _ (mul_ne_zero ha hb), length_span _ ha, length_span _ hb,
    IsDiscreteValuationRing.addVal_mul]
  have h1 : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have h2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  rw [ENat.toNat_add h1 h2]
  push_cast
  rw [add_div]

variable {D : D7}

theorem act_bc_eig (i : D.nd.Loc) (f : D.nd.T i) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u = ((f : D.nd.X i → D.nd.O i) x) • u := by
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h
  rw [h, algebraMap_smul]

theorem bc_mem_eig (i : D.nd.Loc) (β : Module.End (D.nd.O i) (D.nd.Mt i))
    (hβ : ∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    β.baseChange (FractionRing (D.nd.O i)) u ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  refine (Submodule.mem_iInf _).mpr fun f => ?_
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  have e : (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) (β.baseChange (FractionRing (D.nd.O i)) u) =
      β.baseChange (FractionRing (D.nd.O i)) ((D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u) := by
    rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← hβ f, LinearMap.baseChange_mul,
      Module.End.mul_apply]
  rw [e, h, map_smul]

theorem perPoint (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) (h : CutAt i k π Xs β b) :
    ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i Xs π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard := by
  classical
  obtain ⟨_, hπZ, hXZ, hcomm, hb0, hbπ, hbout, hblen⟩ := h
  have hπc : π ∈ cutLocus i Xs := by simp [cutLocus, hπZ]
  obtain ⟨f0, hf0, hf0π⟩ := exists_ne_zero (D.nd.T i) (D.nd.T_sep i) _ π hπc
  obtain ⟨c, hc⟩ : ∃ c, ccAt (D.nd.T i) (cutLocus i Xs) π = Ideal.span {c} :=
    ⟨Submodule.IsPrincipal.generator _, (Ideal.span_singleton_generator _).symm⟩
  have hcI : c ∈ ccAt (D.nd.T i) (cutLocus i Xs) π := hc ▸ Ideal.mem_span_singleton_self c
  obtain ⟨g, hg, hgπ⟩ := exists_of_mem_ccAt _ _ _ hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hm : ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) π).comp (D.nd.T i).val.toRingHom) f0 ∈
        ccAt (D.nd.T i) (cutLocus i Xs) π := Ideal.mem_map_of_mem _ hf0
    rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hm
    exact hf0π hm
  refine ⟨D.nd.act i g * β, c * b, ?_, ?_, mul_ne_zero hc0 hb0, ?_, ?_⟩
  · intro f
    rw [mul_assoc, hcomm f, ← mul_assoc, ← map_mul, mul_comm g f, map_mul, mul_assoc]
  · intro x hx u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply]
    by_cases hxs : x ∈ Xs
    · have hxZ : x ∉ D.nd.Z i := fun hz => hx (hXZ x hxs hz)
      have hxc : x ∉ cutLocus i Xs := by simp [cutLocus, hxZ, hxs]
      rw [act_bc_eig i g x (bc_mem_eig i β hcomm x hu), (mem_ccIdeal_iff _ _ g).mp hg x hxc, zero_smul]
    · rw [hbout x hxs u hu, map_zero]
  · intro u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply, hbπ u hu, LinearMap.map_smul_of_tower,
      act_bc_eig i g π hu, hgπ, smul_smul, mul_comm]
  · unfold vccCut
    rw [lenUnit_mul _ hc0 hb0, ← hc]
    linarith

theorem fam_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ),
    CongruenceLocalDecomposition CT i k ρ eta → CongruenceFamilyEndomorphisms CT i k ρ eta := by
  intro D CT i k ρ eta hcut
  classical
  obtain ⟨Xs, β, b, h⟩ := hcut
  have hp : ∀ π ∈ D.nd.Zgood i, ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i (Xs π) π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard :=
    fun π hπ => perPoint i k π (Xs π) (β π) (b π) (h π hπ).1
  choose! α a hα using hp
  refine ⟨α '' ((D.nd.Zgood i : Finset (D.nd.X i)) : Set (D.nd.X i)), a, fun π => vccCut i (Xs π) π, ?_, ?_⟩
  · rintro _ ⟨π, hπ, rfl⟩
    exact ⟨(hα π hπ).1, (hα π hπ).2.1⟩
  · intro π hπ
    obtain ⟨_, _, h3, h4, h5⟩ := hα π hπ
    exact ⟨h3, ⟨α π, ⟨π, hπ, rfl⟩, h4⟩, h5, (h π hπ).2⟩

end GlobalTheory.CutFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSubOneEq
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildUnipotent

open Polynomial in

theorem exists_pow_sub_one_eq {O : Type} [CommRing O] {n l : ℕ} (hl : l.Prime) (u : Matrix (Fin n) (Fin n) O)
    (hu : u.charpoly = (X - 1) ^ n) (M : ℕ) :
    ∃ c : Matrix (Fin n) (Fin n) O, u ^ (l ^ (n + M)) - 1 = ((l : O) ^ (M + 1)) • c := by
  have h0 : (u - 1) ^ n = 0 := by
    have := Matrix.aeval_self_charpoly u
    rw [hu] at this
    simpa using this
  have h1 : (u - 1) ^ (l ^ n) = 0 := pow_eq_zero_of_le (Nat.lt_pow_self hl.one_lt).le h0
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (1 : O[X]) (X - 1) n
  have h2 : (l : O[X]) ∣ X ^ (l ^ n) - (1 + (X - 1) ^ (l ^ n)) := by
    rw [add_sub_cancel, one_pow] at hr
    rw [hr, add_sub_cancel_left, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub h2 M
  refine ⟨aeval u c, ?_⟩
  have h3 := congrArg (aeval u) hc
  simp only [map_sub, map_pow, map_add, map_one, aeval_X, h1, add_zero, one_pow, map_mul, map_natCast] at h3
  rw [pow_add, pow_mul, h3, Algebra.smul_def, map_pow, map_natCast]

theorem eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : ¬ A.valuation (l : Ω) < 1)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (had : IsAdic (IsLocalRing.maximalIdeal O)) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (r : G E Ω →* GL (Fin n) O)
    (hr : Continuous (fun g => ((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1)
    (hc : ((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).charpoly = (Polynomial.X - 1) ^ n) : r σ = 1 := by
  have key : ∀ M : ℕ, ∀ a b, (((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
      IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)
    let H : Subgroup (G E Ω) := ((Matrix.GeneralLinearGroup.map q).comp r).ker
    have hH : ∀ g, g ∈ H ↔ ∀ a b, (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
        IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      have e : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M) ((1 : Matrix (Fin n) (Fin n) O) a b) =
          (1 : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O ^ M)) a b := by
        by_cases h : a = b <;> simp [Matrix.one_apply, h]
      rw [e]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = ⋂ a, ⋂ b,
          (fun g => (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b) ⁻¹'
            ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
        exact hH g
      rw [e]
      refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
      exact ((isAdic_iff.1 had).1 M).preimage ((hr.sub continuous_const).matrix_elem a b)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ (l ^ (n + M)) ?_ hσ ?_)
    · have h1 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, map_pow, h1, one_pow]
      exact lt_irrefl _
    · rw [hH]
      intro a b
      obtain ⟨c, hc'⟩ := exists_pow_sub_one_eq hl _ hc M
      rw [map_pow, Units.val_pow_eq_pow_val, hc', Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlO M)
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  ext a b
  have h2 := Ideal.mem_iInf.2 fun M => key M a b
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem main : ∀ (D : D7) (i : D.nd.Loc) (n : ℕ) (r : GE D.nd →* GL (Fin n) (D.nd.O i)), Continuous (fun g => ((r g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) → ∀ v : HeightOneSpectrum (𝓞 D.host.E), v ∉ placesOver D.host.E (D.nd.l i) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), ((r σ : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i)).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro D i n r hr v hv σ hσ hc
  have := D.nd.trO i
  refine eq_one_of_wild (D.nd.plOm.1 v) (l := D.nd.l i) Fact.out ?_ (D.nd.O_adic i)
    (GlobalTheory.WildAdditive.not_isUnit_natCast (D.nd.l i) (D.nd.O i)) r hr σ hσ hc
  intro h
  apply hv
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  rw [← hA]
  simpa using h

end GlobalTheory.WildUnipotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiOperatorEtalePhiGammaModule
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem psi_of_etale_basis {R E M Γ : Type*} [CommRing R] [CommRing E] [Algebra R E]
    [AddCommGroup M] [Module E M] [Module R M] [IsScalarTower R E M]
    (φE : E →+* E) (φD : M →ₗ[R] M) (hφD : ∀ (e : E) (x : M), φD (e • x) = φE e • φD x)
    (γE : Γ → E →+* E) (γD : Γ → M →ₗ[R] M)
    (hγD : ∀ g (e : E) (x : M), γD g (e • x) = γE g e • γD g x)
    (hφγ : ∀ g x, φD (γD g x) = γD g (φD x)) {r : ℕ} (b b' : Module.Basis (Fin r) E M)
    (hb : ∀ j, b' j = φD (b j)) (ψE : E →ₗ[R] E)
    (hψφ : ∀ a x, ψE (φE a * x) = a * ψE x) (hψγ : ∀ g x, ψE (γE g x) = γE g (ψE x))
    (hψone : ψE 1 = 1) :
    ∃ ψ : M →ₗ[R] M, (∀ x, ψ (φD x) = x) ∧
      (∀ (a : E) x, ψ (φE a • x) = a • ψ x) ∧ ∀ g x, ψ (γD g x) = γD g (ψ x) := by
  let ψ : M →ₗ[R] M :=
    { toFun := fun z => ∑ j, ψE (b'.repr z j) • b j
      map_add' := fun z w => by
        simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul E c z, map_smul, Finsupp.smul_apply, smul_eq_mul,
          ← Algebra.smul_def, map_smul, smul_assoc] }
  have hψ : ∀ z, ψ z = ∑ j, ψE (b'.repr z j) • b j := fun z => rfl
  have hdec : ∀ z : M, z = ∑ j, b'.repr z j • φD (b j) := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    simp only [hb]
  have hkey : ∀ (x : E) (y : M), ψ (x • φD y) = ψE x • y := by
    intro x y
    have hy : φD y = ∑ j, φE (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      simp only [hφD, hb]
    rw [hψ, hy, Finset.smul_sum]
    simp only [smul_smul]
    rw [b'.repr_sum_self]
    conv_rhs => rw [← b.sum_repr y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, hψφ, smul_smul, mul_comm]
  refine ⟨ψ, fun x => ?_, fun a z => ?_, fun g z => ?_⟩
  · have := hkey 1 x
    rwa [one_smul, hψone, one_smul] at this
  · rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hψφ, mul_smul]
  · rw [hψ z, map_sum]
    conv_lhs => rw [hdec z, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγD, ← hφγ, hkey, hψγ, hγD]

set_option maxHeartbeats 2000000 in

theorem psiD_exists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  intro D HW F l _ K s LL h W T
  obtain ⟨r, b, b', hb⟩ := GlobalTheory.T.wachEtaleModule_frobenius_basis D HW F l K s LL h T
  obtain ⟨ψE, hψφ, hψγ, hψ1⟩ := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K s LL h
  have hψone : ψE 1 = 1 := by
    have := hψ1 0 (Fact.out : l.Prime).pos 1
    simpa using this
  exact psi_of_etale_basis (W.φE : W.EE →+* W.EE) (W.φD T) (W.φD_smul T)
    (fun g => (W.γE g : W.EE →+* W.EE)) (W.γD T) (W.γD_smul T) (W.φγ_comm T) b b' hb ψE hψφ hψγ hψone

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundameStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  first | exact @GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | exact GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | (intros; apply GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChangeStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalSelmerCocycle_baseChange : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  first | exact @GlobalTheory.NewPrime.UnivCocycle.main | exact GlobalTheory.NewPrime.UnivCocycle.main | (intros; apply GlobalTheory.NewPrime.UnivCocycle.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperUnitriangularEntriesHomeomorphStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  first | exact @GlobalTheory.UnipCoords.unipCoordsHomeomorph | exact GlobalTheory.UnipCoords.unipCoordsHomeomorph | (intros; apply GlobalTheory.UnipCoords.unipCoordsHomeomorph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobeniusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y → ∀ g : GQ l, Per.σC g y = y := by
  first | exact @GlobalTheory.RegularDense.fixed_of_inertia_frobenius | exact GlobalTheory.RegularDense.fixed_of_inertia_frobenius | (intros; apply GlobalTheory.RegularDense.fixed_of_inertia_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Decompl

theorem fontaine_and_decompletion :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F :=
  fun D HW F l _ K s LL h =>
    ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOneStatement
section
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobXi_div_prime_unit_tendsto_one : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l), ∃ u : Per.Acris l, IsUnit u ∧ (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧ ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  first | exact @GlobalTheory.MemLoc.phi_xi_unit_tendsto | exact GlobalTheory.MemLoc.phi_xi_unit_tendsto | (intros; apply GlobalTheory.MemLoc.phi_xi_unit_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegreeStatement
section
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l, (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 → (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) → IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  first | exact @GlobalTheory.MemLoc.EigenDegree.main | exact GlobalTheory.MemLoc.EigenDegree.main | (intros; apply GlobalTheory.MemLoc.EigenDegree.main <;> assumption)
end

