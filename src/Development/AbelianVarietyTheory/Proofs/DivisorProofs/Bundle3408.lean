import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianIsAbelianSchemeLocalizationAbelianLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusAtPrime

theorem isAbelianScheme_localization : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  intro R _ _ _ G₁ _ _ hG p _ hp
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  set f := spMap (algebraMap R (Localization.AtPrime p.asIdeal)) with hf
  have hG' : IsSemiAbelian ((Over.pullback f).obj G₁) := IsSemiAbelian.pullback f G₁ hG
  have hopen : IsOpen (abLocus G₁) := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G₁ hG
  have hgen : ∀ z : Sp (Localization.AtPrime p.asIdeal), f z ∈ abLocus G₁ := by
    intro z
    have hle : (f z) ⤳ p := by
      refine (PrimeSpectrum.le_iff_specializes (R := R) (f z) p).1 ?_
      have hr : (f z : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) := by
        exact ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl] at hr
      show (f z : PrimeSpectrum R).asIdeal ≤ (p : PrimeSpectrum R).asIdeal
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.1 hr hxp hx
    exact hle.mem_open hopen hp
  have hab : abLocus ((Over.pullback f).obj G₁) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 (hgen z)
  exact
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' hab
      geomConnected := hG'.geomConnected }

end GlobalTheory.AbLocusAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupSchemeHomTangentAtOriginSurjectiv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieSurjLocal

theorem map_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q], Smooth q.left → ∀ u : TanM (𝟙 (Sp R)) B, ∃ v : TanM (𝟙 (Sp R)) G, tv v ≫ q = tv u := by
  intro R _ _ G B _ _ _ _ q _ hsm u
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  let π : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have hu : Spec.map π ≫ (tv u).left = η[B].left := GlobalTheory.RayBasis.isTangent_pt u
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ (tv u).left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans hu.symm
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint R)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π
    (tv u).left η[G].left h0
    (GlobalTheory.range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := .of_surjective _ hπ
      have e : q.left (η[G].left (IsLocalRing.closedPoint R)) =
        (tv u).left (Spec.map π (IsLocalRing.closedPoint R)) := congr($h0 (IsLocalRing.closedPoint R))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (GlobalTheory.range_subset_opens_of_isLocalRing _ hxV) (by
      intro R' S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  let xo : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G :=
    Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w (tv u))
  have hz : smT (𝟙 (Sp R)) 0 xo = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap _ ≫ x = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ _
    rw [Category.comp_id, ← hx, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    ext <;> simp [π, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT xo hz, Over.OverMorphism.ext hq⟩

end GlobalTheory.LieSurjLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapDualMapCompEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

open GlobalTheory.LogKSBal GlobalTheory.KS GlobalTheory.TangentOrigin

theorem spMap_resV (R : Type) [CommRing R] (c : R) : spMap (resV R c) = chart (bo R c) := by
  have h := (isAffineOpen_top (Sp R)).map_fromSpec (bo R c).2
    (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

theorem exists_isTr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) : ∃ w, IsTr G φ g v w := by
  have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := (Over.w (tv v)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
    show _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom
    rw [Category.assoc, h1, hg, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨_, Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g) (Category.assoc _ _ _),
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2, rfl, rfl, rfl⟩

theorem spMap_dualMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem ksRel_operators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (h.trans (inf_le_left.trans (hW i))) (Θ₁ a b) * (dd' b O (rsT (t.PP.L.g (j i) (j i')).val O) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val O) * dd' a O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt _ _ c _ n v' dd' hdd DV Θ₁ hKS
  obtain ⟨J, W, j, d, hcov, hWj, hfld, hlift, hdiff⟩ := hKS
  rw [inf_idem] at hcov
  have hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := fun i => (le_iSup W i).trans hcov.le
  refine ⟨J, W, j, d, hW, hcov, hWj, hfld, fun i O h a => ?_, fun i i' O h f => ?_⟩
  · have e : ∀ s : Γ(Sp R, (bo R c).1), cst t.G.hom _ (h.trans (hW i)) s = resG _ h (cst t.G.hom _ (hW i) s) := fun s => by
      rw [← rsT_of_le h, ← pbT_of_le, ← pbT_of_le, rsT_pbT t.G.hom (hW i) h]
    rw [e, e, (hfld i).2.2 _ _ h le_rfl, hlift]
  · refine ext_valR _ _ fun S _ x hx => ?_
    have hO : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := h.trans (inf_le_left.trans (hW i))
    have hr : Set.range (x ≫ t.G.hom) ⊆ Set.range (chart (bo R c)) := by
      rintro _ ⟨p, rfl⟩
      exact (bo R c).2.range_fromSpec.superset (hO (hx (Set.mem_univ p)))
    have : IsOpenImmersion (chart (bo R c)) := (bo R c).2.isOpenImmersion_fromSpec
    obtain ⟨φ, hφ⟩ : ∃ φ : Γ(Sp R, (bo R c).1) →+* S, x ≫ t.G.hom = spMap φ ≫ chart (bo R c) :=
      ⟨(Spec.preimage (IsOpenImmersion.lift _ _ hr)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
    have hφ' : x ≫ t.G.hom = spMap (φ.comp (resV R c)) := by
      rw [hφ, ← spMap_resV, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    choose w hw using fun a => exists_isTr t.G _ x hφ' (v' a)
    have key := hdiff i i' O h f S φ x w hφ hx fun a => by
      obtain ⟨g', u, h₁, h₂, h₃⟩ := hw a
      exact ⟨g', u, h₁, by rw [h₂, spMap_dualMap_comp_eq, Category.assoc], h₃⟩
    have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (h hp).1, hWj i' (h hp).2⟩
    have hxg : ⊤ ≤ x ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) := fun p hp => hOg (hx hp)
    rw [key, valR_eq x hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_mul, ← valR_eq, ← valR_eq, ← valR_eq, ← valR_eq,
      (hdd a).2 S _ x (w a) O f hφ' hx (hw a), (hdd b).2 S _ x (w b) _ _ hφ' hxg (hw b), valR_rsT x hOg hx,
      rsT_of_le hOg, (hdd b).1.2.2 _ _ hOg le_top, ← rsT_of_le hOg, valR_rsT x hOg hx, ← pbT_of_le,
      valR_pbT x _ hO hx, hφ, valR_chart]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SignSym

section Move
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_gen_onA (U : UnifPre I D A G) {n : ℕ} (fG : Fin n → (G ⟶ G)) (fA : Fin n → (A.A ⟶ A.A))
    (hf : ∀ k, (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = U.gen.hom ≫ fA k) (ε : Fin n → ℤ)
    (φ : Fin n → (G.left ⟶ G.left)) (hφ : ∀ k, φ k = (fG k).left)
    (φA : Fin n → (A.A.left ⟶ A.A.left)) (hφA : ∀ k, φA k = (fA k).left)
    (t : LB.Gen (LB.LinComb U.LG.L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb A.L φA ε), a.IsGen := by
  obtain ⟨w, hw⟩ := U.ext
  let π : A.A ⟶ (Over.pullback (jK R)).obj G := U.gen.inv
  obtain ⟨a, ha, -⟩ := H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw)
    φ (fun k => (π ≫ (Over.pullback (jK R)).map (fG k)).left) ε (π.left ≫ pullback.fst G.hom (jK R))
    (fun k => by
      rw [hφ k]
      exact (Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)) t ht
  obtain ⟨b, hb⟩ := PsiPull.exists_gen_flat _ _ _ a ha
  obtain ⟨α, hα, -⟩ := exists_gen A.isLB (φ' := φA) (ε' := ε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by
      have e : π ≫ (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = fA k := by
        rw [hf k, ← Category.assoc, U.gen.inv_hom_id, Category.id_comp]
      rw [hφA k]
      exact congrArg (fun q : A.A ⟶ A.A => h q.left ^ ε k) e) b hb
  exact ⟨α, hα⟩

end Move
end GlobalTheory.SignSym

namespace GlobalTheory.SignSym

theorem sign_sym : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  intro R _ _ _ I hI D A G _ _ hG U O _ _ _ o oA oG hlin w hw
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := U.gen_hom
  haveI := oG.hom w
  haveI := oA.hom w
  obtain ⟨-, E, eG, eA, -, -, -⟩ := IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U
  have rId : (Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom = U.gen.hom ≫ 𝟙 A.A := by
    rw [(Over.pullback (jK R)).map_id, Category.id_comp, Category.comp_id]
  have rW : (Over.pullback (jK R)).map (oG.act w) ≫ U.gen.hom = U.gen.hom ≫ oA.act w := hlin.ext w
  have rInv : (Over.pullback (jK R)).map (ι[G]) ≫ U.gen.hom = U.gen.hom ≫ ι[A.A] := by
    have h := E.ext
    rw [eG, eA, Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at h
    exact h
  have rOne : (Over.pullback (jK R)).map (1 : G ⟶ G) ≫ U.gen.hom = U.gen.hom ≫ (1 : A.A ⟶ A.A) := by
    rw [(Over.pullback (jK R)).map_one, MonObj.one_comp, MonObj.comp_one]
  have rSum : (Over.pullback (jK R)).map (𝟙 G * oG.act w) ≫ U.gen.hom = U.gen.hom ≫ (𝟙 A.A * oA.act w) := by
    rw [(Over.pullback (jK R)).map_mul, MonObj.mul_comp, MonObj.comp_mul, rId, rW]

  obtain ⟨σ₀, hσ₀⟩ := exists_gen_onA U.toUnifPre ![ι[G], 𝟙 G] ![ι[A.A], 𝟙 A.A]
    (fun k => by fin_cases k; exacts [rInv, rId]) ![1, -1] _ (fun k => by fin_cases k <;> rfl)
    ![(ι[A.A]).left, 𝟙 A.A.left] (fun k => by fin_cases k <;> rfl) U.symG U.symG_gen
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hw
  obtain ⟨β, hβ⟩ := exists_gen_onA U.toUnifPre ![𝟙 G, 𝟙 G * oG.act w, 𝟙 G, oG.act w, 1]
    ![𝟙 A.A, 𝟙 A.A * oA.act w, 𝟙 A.A, oA.act w, 1]
    (fun k => by fin_cases k; exacts [rId, rSum, rId, rW, rOne]) GlobalTheory.JetSer.primε (GlobalTheory.JetSer.primφ (oG.act w)) (fun k => by fin_cases k <;> rfl)
    (GlobalTheory.JetSer.primφ (oA.act w)) (fun k => by fin_cases k <;> rfl) ρ hρ

  let z₀ : A.A ⟶ A.A := 1
  have o₁ : z₀.left ≫ (ι[A.A]).left = z₀.left := by
    rw [← Over.comp_left, ← Hom.inv_def, inv_one]
  have o₂ : z₀.left ≫ 𝟙 A.A.left = z₀.left := Category.comp_id _
  obtain ⟨σ, hσ, vσ⟩ := exists_gen A.isLB (φ' := ![(ι[A.A]).left, 𝟙 A.A.left]) (ε' := ![1, -1])
    (fun V _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂]
      rw [neg_neg, ← zpow_add, neg_add_cancel, zpow_zero, _root_.mul_one])
    (LB.mulGen A.L _ _ _ _ σ₀ (LB.invGen A.L _ _ (LB.pullGen A.L _ _ σ₀ z₀.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hσ₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hσ₀ _)))
  have vσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) z J, Good A.L z J →
      val σ r z J = val σ₀ r z J * (val σ₀ (r ≫ z₀.left) z J)⁻¹ :=
    fun Z r z J hJ => (vσ Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A) = η[A.A] := by simp [Hom.one_def]
  have e₀ : eSec A.A ≫ z₀.left = eSec A.A := by
    show η[A.A].left ≫ (1 : A.A ⟶ A.A).left = η[A.A].left
    rw [← Over.comp_left, MonObj.comp_one, e₁]
  have hσ1 : ∀ y J, Good A.L y J → val σ (eSec A.A) y J = 1 := fun y J hJ => by
    rw [vσ' _ _ y J hJ, e₀, mul_inv_cancel]
  have hσn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) :=
    corr_of_val A.isLB fun y J hJ => by
      rw [val_pull hJ, Category.id_comp, val_one]
      exact hσ1 y J hJ
  refine ⟨σ, hσ, hσn, fun T x hx z J hJ => ?_⟩

  have hY : Function.Surjective A.A.hom.appTop.hom := (hGF _ _ A.isAb).2
  have hι : ι[A.A] = (𝟙 A.A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have hinv : ∀ {Y : Over (Spec (CommRingCat.of (FractionRing R)))} (f : Y ⟶ A.A), f ≫ ι[A.A] = f⁻¹ := fun f => by
    rw [Hom.inv_def]
  have c₁ : ι[A.A] ≫ oA.act w = oA.act w ≫ ι[A.A] := by
    have := IntEnd.id_zpow_comm (oA.act w) (-1)
    rw [zpow_neg_one, ← hι] at this
    exact this
  have c₂ : ι[A.A] ≫ (𝟙 A.A * oA.act w) = (𝟙 A.A * oA.act w) ≫ ι[A.A] := by
    rw [MonObj.comp_mul, Category.comp_id, c₁, hinv, hinv, mul_inv, hι]
  have nv : ∀ y I, Good A.L y I → val σ (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A).left y I = 1 :=
    fun y I hI => by rw [e₁]; exact hσ1 y I hI
  have H := ((SymFrame.hasGen_pull hβ (𝟙 A.A)).mul (SymFrame.hasGen_pull hβ (ι[A.A])).inv).unique A.isLB
    ((((SymFrame.hasGen_pull hσ (𝟙 A.A * oA.act w)).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul
      (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (oA.act w)).inv)
    (fun V _ h => ?_) hY 1 (fun y I hI => ?_) T x z J hJ
  · have xi : x ≫ ι[A.A] = x := by
      rw [hinv]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
    have xs : x ≫ (𝟙 A.A * oA.act w) = x * (x ≫ oA.act w) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [xi, xs, Category.comp_id, mul_inv_cancel] at H
    apply Additive.ofMul.injective
    have a := congrArg Additive.ofMul H
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a ⊢
    calc _ = (Additive.ofMul (val σ (x * x ≫ oA.act w).left z J) + -Additive.ofMul (val σ x.left z J) +
          -Additive.ofMul (val σ x.left z J) + -Additive.ofMul (val σ (x ≫ oA.act w).left z J)) +
          (2 • Additive.ofMul (val σ x.left z J) + Additive.ofMul (val σ (x ≫ oA.act w).left z J)) := by abel
      _ = _ := by rw [← a, zero_add]
  · simp only [GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, Fin.prod_univ_five, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
      Over.id_left, Category.id_comp, Category.comp_id, ← Over.comp_left, c₁, c₂, MonObj.comp_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  · rw [Category.comp_id, hinv, inv_one, MonObj.comp_mul, Category.comp_id, MonObj.one_comp, _root_.mul_one,
      mul_inv_cancel, nv y I hI]
    simp

end GlobalTheory.SignSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanBasisPull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BasisPull

theorem tanBasis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ T.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t.G.left)), (∀ i, IsTanAtG T (chart U) (v i)) → (∀ w, IsTanAtG T (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG T (chart U) v cf w) → (∀ i, IsTanAtG t (chart U') (v' i)) → (∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ w, IsTanAtG t (chart U') w → ∃! cf : Fin n → Γ(X', U'.1), IsCombAtG t (chart U') v' cf w := by
  intro E _ _ _ H X X' T t g φ U U' hU n v v' hv hvb hv' hvv' w hw
  have hx : chart U' ≫ g = spMap (g.appLE U.1 U'.1 hU).hom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
  obtain ⟨v'', hv''φ, hv''t, hv''b⟩ :=
    GlobalTheory.SabTan.tanBasis_sabMap E H X X' T t g φ _ _ (g.appLE U.1 U'.1 hU).hom (chart U) (chart U')
      hx n v hv hvb
  have heq : v'' = v' := by
    funext i
    apply φ.cart.1.hom_ext
    · rw [hv''φ, hvv']
    · rw [(hv''t i).1, (hv' i).1]
  rw [← heq]
  exact hv''b w hw

end GlobalTheory.BasisPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add, LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by
      rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRayBasis

theorem vBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  obtain ⟨b, hb⟩ := GlobalTheory.TanRay.tanBasis_of_isPointOf E H R t P Y n vH v' hv
  exact ⟨b, funext hb⟩

end GlobalTheory.TanRayBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxIdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  first | exact @GlobalTheory.Poinc.LamBound.main | exact GlobalTheory.Poinc.LamBound.main | (intros; apply GlobalTheory.Poinc.LamBound.main <;> assumption)
end

