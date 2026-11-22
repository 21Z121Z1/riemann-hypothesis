import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem lift_of_stalk_generic_flat : ∀ {X' W : Scheme.{0}} [IsIntegral X'] (h : W ⟶ X') [Flat h] (q : W)
    [IsDomain (W.presheaf.stalk q)] {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ]
    (Ω : Type) [Field Ω] (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (hy : ∀ x, (y x).asIdeal = ⊥), ∃ z : Sp Ω ⟶ V, y ≫ W.fromSpecStalk q ≫ h = z ≫ ℓ := by
  intro X' W _ h _ q _ V _ ℓ _ Ω _ y hy
  have hinj : Function.Injective (h.stalkMap q).hom := by
    letI := (h.stalkMap q).hom.toAlgebra
    haveI : Module.Flat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) := Flat.stalkMap h q
    haveI : IsLocalHom (algebraMap (X'.presheaf.stalk (h q)) (W.presheaf.stalk q)) :=
      (inferInstance : IsLocalHom (h.stalkMap q).hom)
    haveI : Module.FaithfullyFlat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  have hrange : Set.range (y ≫ W.fromSpecStalk q ≫ h) ⊆ Set.range ℓ := by
    rintro _ ⟨x, rfl⟩
    have key : (y ≫ W.fromSpecStalk q ≫ h) x =
        X'.fromSpecStalk (h q) (Spec.map (h.stalkMap q) (y x)) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; rfl
    rw [key]
    set p : Spec (X'.presheaf.stalk (h q)) := Spec.map (h.stalkMap q) (y x) with hpdef
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap (h.stalkMap q).hom (y x).asIdeal = ⊥
      rw [hy x]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨s, hs⟩ : genericPoint X' ∈ Set.range (X'.fromSpecStalk (h q)) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X').specializes (Set.mem_univ _)
    have hps : p ⤳ s := (PrimeSpectrum.le_iff_specializes _ _).1 (by
      show p.asIdeal ≤ s.asIdeal
      rw [hp]; exact bot_le)
    have hgen : genericPoint X' ∈ Set.range ℓ :=
      ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).2
        (by simpa using Set.range_nonempty ℓ)
    have := (hps.map (X'.fromSpecStalk (h q)).continuous).mem_open
      ℓ.isOpenEmbedding.isOpen_range (by rw [hs]; exact hgen)
    exact this
  exact ⟨IsOpenImmersion.lift ℓ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformation
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem cechPt_over (P : GPt A) : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
  (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w

@[reducible] def Pt.cst (P : GPt A) : GPt A where
  B := DualNumber P.B
  x := spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x
  w := (congrArg (_ ≫ ·) (Category.comp_id A.hom)).trans (by
    rw [Category.assoc, cechPt_over, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

theorem Pt.In.cst {P : GPt A} {U : A.left.Opens} (h : P.In U) : P.cst.In U :=
  fun _ _ ↦ h (Set.mem_univ _)

theorem cst_base (P : GPt A) :
    (dualMap (algebraMap K P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber P.B) := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_dualMap (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K (DualNumber P.B)) = algebraMap K P.B := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_inl (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem cst_red (P : GPt A) :
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x = P.x := by
  show _ ≫ spMap _ ≫ P.x = P.x
  rw [← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]

theorem cst_val (P : GPt A) {U : A.left.Opens} (hU : P.In U) (g : Γ(A.left, U)) :
    TrivSqZeroExt.fst (valR P.cst.x U g) = valR P.x U g := by
  show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hU]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem cst_trx_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : P.In U)
    (g : Γ(A.left, U)) : TrivSqZeroExt.fst (valR (P.cst.trx v) U g).snd = (valR (P.trx v) U g).snd := by
  have hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U := hU.cst.tr hv
  have hm := (P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  have e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B :=
    fst_comp_dualMap P
  rw [e1, cst_red] at hm
  rw [← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]
  simp [dualMap]

theorem eps_eq (P : GPt A) :
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra]

theorem cechKS_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  intro K _ A _ A' _ i L n u θ hu h
  obtain ⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩ := h
  have hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
      P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) :=
    fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)
  refine ⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x,
    hcov, hWc, ?_, ?_, ?_⟩
  · intro k P hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    obtain ⟨h1, h2, -⟩ := hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst
    refine ⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩
    let I := Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}
    have hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [eps_eq P]
      simp
    have hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) =
        (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) := RingHom.ext fun _ ↦ rfl
    calc spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ _
        = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x := by
          rw [← Category.assoc, ← Cris.spMap_comp, hq]
      _ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]
      _ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]
      _ = P.x ≫ i := by rw [cst_red]
  · intro k P Q φ hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra
    let ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B :=
      { dualMap (φ.ρ : P.B →+* Q.B) with
        commutes' := fun r ↦ by
          ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }
    have h3 := (hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ
    have hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x := by
      show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
      rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
    exact h3.trans (congrArg _ hc)
  · intro k k' P U f hk hk' hU
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    have ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)))
        P.cst.x (u a) (P.cst.trx (u a)) := fun a ↦ by
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      exact P.cst.isTransl_trx (u a)
    have hd := hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst)
      hU.cst ht
    refine hd.trans ?_
    have hg : P.In (L.U (c k) ⊓ L.U (c k')) := (hk.mono (hWc k)).inf (hk'.mono (hWc k'))
    have e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd =
        (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd := fun a ↦ cst_trx_val P (hu a) hg _
    have e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd =
        (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd := fun a ↦ cst_trx_val P (hu a) hU _
    have e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val :=
      cst_val P hg _
    have e4 : ∀ r : K, TrivSqZeroExt.fst
        (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r := by
      intro r
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [eps_eq P]
    have hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst := fun S ↦ by
      ext <;> simp
    rw [hS]
    congr 1
    change (TrivSqZeroExt.fstHom K P.B P.B) _ = _
    simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]
    simp only [e1, e2, e3, e4, dlog, Finset.sum_mul]

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoConst

theorem lbIso_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left), P.IsLB → M.IsLB → LBIso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) → LBIso P M := by
  intro W K' _ _ _ _ _ _ G _ hG P M hP hM h
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom inferInstance inferInstance
  let ψ : K' ≃ₐ[W] FractionRing W := IsLocalization.algEquiv (nonZeroDivisors W) K' (FractionRing W)
  have e₂ : Out.jK W ≫ 𝟙 _ = spMap (ψ : K' →+* FractionRing W) ≫ spMap (algebraMap W K') := by
    have hr : (ψ : K' →+* FractionRing W).comp (algebraMap W K') = algebraMap W (FractionRing W) := by
      ext x; simp
    rw [Category.comp_id, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have h' : LBIso (P.pull (pullback.fst G.hom (Out.jK W))) (M.pull (pullback.fst G.hom (Out.jK W))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp
      (pullback.map G.hom (Out.jK W) G.hom (spMap (algebraMap W K')) (𝟙 _) (spMap (ψ : K' →+* FractionRing W)) (𝟙 _)
        (by simp) e₂) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm h
  exact GlobalTheory.lbIso_of_generic_normal_local W inferInstance inferInstance G.left G.hom (eSec G) inferInstance inferInstance
    inferInstance (Over.w η[G]) P M hP hM h'

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh TopologicalSpace Opposite in

theorem globalFn_eq_cst : ∀ (W K' : Type) [CommRing W] [Field K'] [Algebra W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ f : Γ(pullback G.hom (spMap (algebraMap W K')), ⊤), ∃ c : K', f = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ c := by
  intro W K' _ _ _ G _ hG f
  have hU := GlobalTheory.AbCoh.uConst_of_isAbelianScheme W G hG K' (pullback G.hom (spMap (algebraMap W K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) (pullback.fst G.hom (spMap (algebraMap W K')))
    (IsPullback.of_hasPullback _ _)
  let g : C0 (OAff (pullback.snd G.hom (spMap (algebraMap W K')))) := fun T =>
    ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE le_top).op).hom f
  have hg : d0 _ g = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    rw [Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_eq_zero]
    exact Sec.res_res (pullback.snd G.hom (spMap (algebraMap W K'))) le_top (leOfHom φ.unop) f
  obtain ⟨r, hr, -⟩ := hU g hg
  refine ⟨r, TopCat.Presheaf.section_ext (pullback G.hom (spMap (algebraMap W K'))).sheaf ⊤ _ _ fun x hx => ?_⟩
  obtain ⟨U, hUa, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp (pullback G.hom (spMap (algebraMap W K'))).isBasis_affineOpens hx
  have e1 : ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f =
      ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r) := by
    refine (hr (op ⟨U, hUa⟩)).trans ?_
    show _ = GlobalTheory.AbLaw.rs _ (le_top : U ≤ ⊤) (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
    rw [GlobalTheory.AbLaw.rs_cst]
    rfl
  have h1 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU f
  have h2 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU
    (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
  exact h1.symm.trans ((congrArg _ e1).trans h2)

theorem exists_iso_const_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro W K' _ _ _ _ _ _ G _ hG P M N hP hM hN w w₁ hw hw₁
  have hP' := pull_isLB hP (pullback.fst G.hom (spMap (algebraMap W K')))
  have hM' := pull_isLB hM (pullback.fst G.hom (spMap (algebraMap W K')))
  obtain ⟨v, hv⟩ := lbIso_of_generic W K' G hG P M hP hM (LBIso.trans hP' hN hM' ⟨w₁, hw₁⟩ (LBIso.symm ⟨w, hw⟩))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos _ _ _ P M N hP hM hN w w₁ v hw hw₁ hv
  obtain ⟨c, hc⟩ := globalFn_eq_cst W K' G hG u.val
  refine ⟨v, c, hv, fun n i m hle => ?_⟩
  rw [hu n i m hle, hc, GlobalTheory.AbLaw.rs_cst]

end GlobalTheory.GenericIsoConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalSectionFamilyUnitAtPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.SemiLoc

variable {X : Scheme.{0}}

theorem exists_pow_mul_eq_zero_of_germ {V : X.Opens} (hV : IsAffineOpen V) (h s : Γ(X, V))
    (H : ∀ z (hz : z ∈ V), z ∈ X.basicOpen h → (X.presheaf.germ V z hz).hom s = 0) :
    ∃ m : ℕ, h ^ m * s = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hV
  apply TopCat.Presheaf.section_ext X.sheaf
  intro z hz
  simp only [TopCat.Presheaf.restrictOpen, map_zero]
  erw [TopCat.Presheaf.germ_res_apply]
  exact (H z (X.basicOpen_le h hz) hz).trans (map_zero _).symm

theorem exists_germ_eq_pow_mul {V O : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hO : X.basicOpen h ≤ O) (r : Γ(X, O)) :
    ∃ (n : ℕ) (y : Γ(X, V)), ∀ z (hz : z ∈ X.basicOpen h),
      (X.presheaf.germ V z (X.basicOpen_le h hz)).hom y =
        (X.presheaf.germ V z (X.basicOpen_le h hz)).hom h ^ n *
          (X.presheaf.germ O z (hO hz)).hom r := by
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV h
    ((X.presheaf.map (homOfLE hO).op).hom r)
  refine ⟨n, y, fun z hz => ?_⟩
  have := congrArg (X.presheaf.germ (X.basicOpen h) z hz).hom hy
  simp only [TopCat.Presheaf.restrictOpen, map_mul, map_pow] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem germ_cocycle {L : LB X} (hL : L.IsLB) (a b c : L.ι) (z : X) (ha : z ∈ L.U a)
    (hb : z ∈ L.U b) (hc : z ∈ L.U c) :
    (X.presheaf.germ (L.U a ⊓ L.U b) z ⟨ha, hb⟩).hom (L.g a b).val *
      (X.presheaf.germ (L.U b ⊓ L.U c) z ⟨hb, hc⟩).hom (L.g b c).val =
    (X.presheaf.germ (L.U a ⊓ L.U c) z ⟨ha, hc⟩).hom (L.g a c).val := by
  have := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ =>
    (X.presheaf.germ (L.U a ⊓ L.U b ⊓ L.U c) z ⟨⟨ha, hb⟩, hc⟩).hom u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul, res, Units.coe_map] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

end GlobalTheory.Pinch.SemiLoc

namespace GlobalTheory.Pinch.SemiLoc

theorem exists_secFam_isUnit_germ : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ (J : Type) [Fintype J] (f : J → Γ(X, W)) (k : J → L.ι) (hk : ∀ j, X.basicOpen (f j) ≤ L.U (k j)) (x : X), x ∈ W → ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
  intro X L hL W hW J _ f k hk x hxW
  classical
  obtain ⟨k0, hk0⟩ : ∃ k0, x ∈ L.U k0 := by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le (V := L.U k0) ⟨x, hk0⟩ hxW
  have hDW : ∀ j, X.basicOpen (f j) ≤ W := fun j => X.basicOpen_le (f j)
  let hj : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom h
  have hbj : ∀ j, X.basicOpen (hj j) = X.basicOpen (f j) ⊓ X.basicOpen h :=
    fun j => X.basicOpen_res h _
  have hgj : ∀ j z (hz : z ∈ X.basicOpen (f j)),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (hj j) =
        (X.presheaf.germ W z (hDW j hz)).hom h :=
    fun j z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hO : ∀ j, X.basicOpen (hj j) ≤ L.U (k j) ⊓ L.U k0 := fun j => by
    rw [hbj]; exact inf_le_inf (hk j) hhU
  choose n y hy using fun j =>
    exists_germ_eq_pow_mul (hW.basicOpen (f j)) (hj j) (hO j) (L.g (k j) k0).val
  let N := Finset.univ.sup n
  let e : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => hj j ^ (N - n j) * y j
  have he : ∀ j z (hz : z ∈ X.basicOpen (f j)) (hzh : z ∈ X.basicOpen h),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) =
        (X.presheaf.germ W z (hDW j hz)).hom h ^ N *
          (X.presheaf.germ (L.U (k j) ⊓ L.U k0) z ⟨hk j hz, hhU hzh⟩).hom (L.g (k j) k0).val := by
    intro j z hz hzh
    have hz' : z ∈ X.basicOpen (hj j) := by rw [hbj]; exact ⟨hz, hzh⟩
    have h1 := hy j z hz'
    simp only [e, map_mul, map_pow]
    rw [h1]; simp only [hgj]; rw [← _root_.mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ j))]
  have hdef : ∀ j j', ∃ m : ℕ, ∀ z (hz : z ∈ X.basicOpen (f j)) (hz' : z ∈ X.basicOpen (f j')),
      (X.presheaf.germ W z (hDW j hz)).hom h ^ m *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
    intro j j'
    obtain ⟨V, hVdef⟩ : ∃ V, V = X.basicOpen (f j * f j') := ⟨_, rfl⟩
    have hVeq : V = X.basicOpen (f j) ⊓ X.basicOpen (f j') := hVdef.trans (X.basicOpen_mul _ _)
    have hVa : IsAffineOpen V := hVdef ▸ hW.basicOpen (f j * f j')
    have hV1 : V ≤ X.basicOpen (f j) := hVeq ▸ inf_le_left
    have hV2 : V ≤ X.basicOpen (f j') := hVeq ▸ inf_le_right
    have hVg : V ≤ L.U (k j) ⊓ L.U (k j') := le_inf (hV1.trans (hk j)) (hV2.trans (hk j'))
    have hVW : V ≤ W := hV1.trans (hDW j)
    let d : Γ(X, V) := (X.presheaf.map (homOfLE hV1).op).hom (e j) -
      (X.presheaf.map (homOfLE hVg).op).hom (L.g (k j) (k j')).val *
        (X.presheaf.map (homOfLE hV2).op).hom (e j')
    let hV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom h
    have hbV : X.basicOpen hV = V ⊓ X.basicOpen h := X.basicOpen_res h _
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_germ hVa hV d (by
      intro z hz hzb
      rw [hbV] at hzb
      simp only [d, map_sub, map_mul]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      rw [he j z (hV1 hz) hzb.2, he j' z (hV2 hz) hzb.2,
        ← germ_cocycle hL (k j) (k j') k0 z (hk j (hV1 hz)) (hk j' (hV2 hz)) (hhU hzb.2)]
      ring)
    refine ⟨m, fun z hz hz' => ?_⟩
    have hzV : z ∈ V := by rw [hVeq]; exact ⟨hz, hz'⟩
    have := congrArg (X.presheaf.germ V z hzV).hom hm
    simp only [d, hV, map_mul, map_pow, map_sub, map_zero] at this
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
    exact this
  choose m hm using hdef
  let M := Finset.univ.sup (fun p : J × J => m p.1 p.2)
  refine ⟨fun j => hj j ^ M * e j, ?_, ?_⟩
  · intro j j' z hz hz'
    have hle : m j j' ≤ M := Finset.le_sup (f := fun p : J × J => m p.1 p.2) (Finset.mem_univ (j, j'))
    have h0 := hm j j' z hz hz'
    simp only [map_mul, map_pow]
    simp only [hgj]
    have h2 : (X.presheaf.germ W z (hDW j hz)).hom h ^ M *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc, h0, mul_zero]
    linear_combination h2
  · intro j hx
    have hu : IsUnit ((X.presheaf.germ W x (hDW j hx)).hom h) := (X.mem_basicOpen h x _).1 hxh
    simp only [map_mul, map_pow]
    simp only [hgj]; rw [he j x hx hxh]
    exact (hu.pow _).mul ((hu.pow _).mul ((L.g (k j) k0).isUnit.map _))

end GlobalTheory.Pinch.SemiLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ) (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) → (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) → (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  first | exact @GlobalTheory.Pinch.exists_lb_of_matching_gens | exact GlobalTheory.Pinch.exists_lb_of_matching_gens | (intros; apply GlobalTheory.Pinch.exists_lb_of_matching_gens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFiniteStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  first | exact @GlobalTheory.LBDescent.exists_trivial_near_fibre | exact GlobalTheory.LBDescent.exists_trivial_near_fibre | (intros; apply GlobalTheory.LBDescent.exists_trivial_near_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_finite_cover_near_point : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  first | exact @GlobalTheory.Pinch.locGen_near_fibre_of_finite | exact GlobalTheory.Pinch.locGen_near_fibre_of_finite | (intros; apply GlobalTheory.Pinch.locGen_near_fibre_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generators_residue_basis : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  first | exact @GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective | exact GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective | (intros; apply GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowMemCartierMultipleOfRegularLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_pow_mem_cartierMultiple_of_regular_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ) (s : Y.functionField), s ∈ Sec D k → ∀ g : Y.functionField, (∀ y ∈ locus D k s, RegAt y g) → ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  first | exact @GlobalTheory.Desc.exists_mul_pow_mem_sec | exact GlobalTheory.Desc.exists_mul_pow_mem_sec | (intros; apply GlobalTheory.Desc.exists_mul_pow_mem_sec <;> assumption)
end

