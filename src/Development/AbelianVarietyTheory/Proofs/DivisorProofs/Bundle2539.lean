import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FibreTransfer

theorem exists_residueField_factor (S : Scheme.{0}) (p : S) (K : Type) [Field K] (x : Sp K ⟶ S)
    (hx : x (closedPoint K) = p) :
    ∃ θ : S.residueField p ⟶ CommRingCat.of K, Spec.map θ ≫ S.fromSpecResidueField p = x := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x⟩

theorem isGrpPullback_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    IsGrpPullback ((Over.pullback (Spec.map θ ≫ S.fromSpecResidueField p)).obj G)
      ((Over.pullback (S.fromSpecResidueField p)).obj G) (Spec.map θ)
      (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
        (by rw [pullback.condition, Category.assoc])) := by
  refine (isGrpPullback_pullback G (S.fromSpecResidueField p)).cancel
    ((isGrpPullback_pullback G (Spec.map θ ≫ S.fromSpecResidueField p)).congr rfl
      (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_fibre {S : Scheme.{0}} (G : Over S) {L : LB G.left} (hL : L.IsLB) (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    LBIso (L.pull (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p)))
      ((L.pull (pullback.fst G.hom (S.fromSpecResidueField p))).pull
        (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
          (by rw [pullback.condition, Category.assoc]))) := by
  have e := GlobalTheory.FibreAmple.lbIso_pull_pull hL
    (pullback.lift (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p))
      (pullback.snd G.hom _ ≫ Spec.map θ) (by rw [pullback.condition, Category.assoc]))
    (pullback.fst G.hom (S.fromSpecResidueField p))
  rw [pullback.lift_fst] at e
  exact e.symm

end GlobalTheory.FibreTransfer

open GlobalTheory.FibreTransfer in

theorem GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  intro S G _ hqc hsep hsm L hL K₁ _ z hP hA hK K _ x hx
  generalize hy : z (closedPoint K₁) = y at hx
  obtain ⟨θ₁, hz⟩ := exists_residueField_factor S y K₁ z hy
  obtain ⟨θ, rfl⟩ := exists_residueField_factor S y K x hx
  clear hy
  subst hz
  haveI := hqc; haveI := hsep; haveI := hsm
  have hLy := pull_isLB hL (pullback.fst G.hom (S.fromSpecResidueField y))
  have i₁ : QuasiCompact ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show QuasiCompact (pullback.snd G.hom _) from inferInstance
  have i₂ : IsSeparated ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show IsSeparated (pullback.snd G.hom _) from inferInstance
  have i₃ : Smooth ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show Smooth (pullback.snd G.hom _) from inferInstance
  have hd := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (S.residueField y) K₁ θ₁.hom
    ((Over.pullback (S.fromSpecResidueField y)).obj G) ((Over.pullback (Spec.map θ₁ ≫ S.fromSpecResidueField y)).obj G) _
    (isGrpPullback_fibre G y K₁ θ₁) _ _ hLy (pull_isLB hL _) (lbIso_fibre G hL y K₁ θ₁) hP hA hK
  have h₂ := isGrpPullback_fibre G y K θ
  obtain ⟨w, hw⟩ := lbIso_fibre G hL y K θ
  exact ⟨relAmple_pull h₂.1 hLy (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hd.2.1,
    kTriv_pull h₂ hLy (pull_isLB hL _) ((isGen_iff w).1 hw) hd.2.2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfClosedProper
section
open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B _)) (fun _ => H)

end GlobalTheory.SharpLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_compare : ∀ (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (e : C ⟶ Z) (Q : LB (A ⊗ C).left), GlobalTheory.DualCon.Rep A b' P' → GlobalTheory.DualCon.Rep A e Q → ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧ Same A P' Q (fst B' Z) q := by
  first | exact @GlobalTheory.Pinch.rep_cmp | exact GlobalTheory.Pinch.rep_cmp | (intros; apply GlobalTheory.Pinch.rep_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResGInjectiveOfTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.TupleBundle

theorem resG_injective_of_top {X : Scheme.{0}} {V : X.Opens} (h : ⊤ ≤ V) : Function.Injective (resG X h) := by
  obtain rfl : V = ⊤ := top_unique h
  have e : (homOfLE h : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  intro a b hab
  simpa [resG, e] using hab

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    resG X h2 (resG X h1 a) = resG X (h2.trans h1) a := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h2 : W ≤ V)
    (a : Γ(X, U)) : resG Y h2 ((f.appLE U V h).hom a) = (f.appLE U W (h2.trans h)).hom a := by
  show (f.appLE U V h ≫ Y.presheaf.map _).hom a = _
  rw [Scheme.Hom.appLE_map]

variable {Ω : Type} [Field Ω]

def ev (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Γ(Sp Ω, V) →+* Ω :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (resG (Sp Ω) hV)

theorem ev_injective (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Function.Injective (ev V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective.comp (resG_injective_of_top hV)

theorem ev_resG {V W : (Sp Ω).Opens} (hV : ⊤ ≤ V) (hW : ⊤ ≤ W) (h : W ≤ V) (a : Γ(Sp Ω, V)) :
    ev W hW (resG (Sp Ω) h a) = ev V hV a := by
  simp only [ev, RingHom.comp_apply, resG_resG]

theorem ev_resG_top {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (x : Ω) :
    ev V hV (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x)) = x := by
  have e : (homOfLE (hV.trans le_top) : (⊤ : (Sp Ω).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  simp only [ev, RingHom.comp_apply, resG_resG]
  simp [resG, e]

theorem ev_appLE {X : Scheme.{0}} (x : Sp Ω ⟶ X) {U : X.Opens} {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (h : V ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev V hV ((x.appLE U V h).hom f) = valF x U f := by
  simp only [ev, RingHom.comp_apply, resG_appLE, valF, dif_pos (hV.trans h)]

end GlobalTheory.TupleBundle

namespace GlobalTheory.TupleBundle

theorem exists_lb_of_hasDiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (J : Type)
    [Finite J] (v : J → Ω), M.HasDiv v → ∃ (δ : LB M.Z) (t : J → δ.Sec), δ.IsLB ∧ (⨆ a, nonzeroLocus (t a)) = ⊤ ∧
    (∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z) ∧ ZM.SecCoord δ t M.pt v := by
  intro o Ω _ _ _ M J _ v hv
  let U : {a // v a ≠ 0} → M.Z.Opens := fun k => ⟨{z | M.Div v k.1 z}, M.isOpen_setOf_div v k.1⟩
  have hU : ⨆ k, U k = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi.1⟩, hi⟩
  obtain ⟨g, hLB, hGT⟩ := ZH.RatModel.exists_isLB_genTriv_of_ratios o Ω M {a // v a ≠ 0} U (fun k => v k.1) hU
    (fun k => k.2) (fun k k' z hz => hz.1.2 k'.1)
  let δ : LB M.Z := ⟨{a // v a ≠ 0}, U, g⟩
  have hsec : ∀ a, ∃ σ : δ.Sec, M.HasVal (H := δ) (fun k => v k.1) σ (v a) := fun a =>
    hGT.exists_sec_hasVal (v a) fun k z hz => hz.2 a
  choose t ht using hsec
  have hnz : ∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z := by
    intro a z
    simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨k, hk⟩
      have hzk : z ∈ U k := M.Z.basicOpen_le _ hk
      have hval : valF M.pt (U k) ((t a).f k) = v a / v k.1 := ht a k ⟨z, hzk⟩
      have hu := (ZH.RatModel.isUnit_valF_iff (M := M) hzk ((t a).f k)).2 hk
      rw [ZH.RatModel.isUnit_O_iff] at hu
      simp only [hval] at hu
      obtain ⟨h1, h2⟩ := hu
      have hk0 := k.2
      have ha0 : v a ≠ 0 := (div_ne_zero_iff.1 h1).1
      refine ⟨ha0, fun j => ?_⟩
      have e : v j / v a = (v j / v k.1) * (v a / v k.1)⁻¹ := by field_simp
      rw [e]
      exact mul_mem (hzk.2 j) h2
    · intro h
      refine ⟨⟨a, h.1⟩, ?_⟩
      have hzk : z ∈ U ⟨a, h.1⟩ := h
      rw [← ZH.RatModel.isUnit_valF_iff (M := M) hzk, ZH.RatModel.isUnit_O_iff]
      have hv1 : valF M.pt (U ⟨a, h.1⟩) ((t a).f ⟨a, h.1⟩) = 1 := (ht a ⟨a, h.1⟩ ⟨z, hzk⟩).trans (div_self h.1)
      simp only [hv1, inv_one]
      exact ⟨one_ne_zero, one_mem _⟩
  refine ⟨δ, t, hLB, ?_, hnz, ?_⟩
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hnz i z).2 hi⟩
  · have hgen : ∀ k : {a // v a ≠ 0}, ⊤ ≤ M.pt ⁻¹ᵁ U k := fun k w _ => by
      show M.pt w ∈ U k
      rw [M.pt_apply w]
      exact ZH.RatModel.div_genericPoint (M := M) k.2
    have hW : ∀ j, ⊤ ≤ (δ.pull M.pt).U j := fun j w _ =>
      Set.mem_iInter.2 fun _ => hgen (j PUnit.unit) (x := w) trivial
    let τ : (δ.pull M.pt).Gen := ⟨fun j => Units.map (resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤)).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
        (Units.mk0 (v (j PUnit.unit).1)⁻¹ (inv_ne_zero (j PUnit.unit).2)))⟩
    have hτ : ∀ j, ((τ.s j : Γ(Sp Ω, (δ.pull M.pt).U j)ˣ) : Γ(Sp Ω, (δ.pull M.pt).U j)) =
        resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹) := fun j => rfl
    refine ⟨τ, fun j j' => ?_, fun i j h => ?_⟩
    · have hle : (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' ≤ M.pt ⁻¹ᵁ (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) :=
        le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ => M.pt) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le δ (fun _ => M.pt) j' PUnit.unit))
      have e0 : (δ.pull M.pt).g j j' = Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) :=
        (Fintype.prod_unique fun _ : PUnit.{1} =>
          Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
      have hne : ((U (j PUnit.unit) ⊓ U (j' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2,
          ZH.RatModel.div_genericPoint (M := M) (j' PUnit.unit).2⟩
      have hg := hGT.g_eq (j PUnit.unit) (j' PUnit.unit) hne
      have hV : ⊤ ≤ (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' := le_inf (hW j) (hW j')
      refine Units.ext (ev_injective _ hV ?_)
      rw [e0]
      show ev _ hV (resG (Sp Ω) inf_le_left (τ.s j : Γ(Sp Ω, _))) =
        ev _ hV ((M.pt.appLE _ _ hle).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) *
          resG (Sp Ω) inf_le_right (τ.s j' : Γ(Sp Ω, _)))
      rw [map_mul, ev_resG (hW j), ev_resG (hW j'), ev_appLE, hτ, hτ, ev_resG_top, ev_resG_top]
      have h1 := (j PUnit.unit).2
      have h2 := (j' PUnit.unit).2
      have hg' : valF M.pt (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) =
          v (j' PUnit.unit).1 / v (j PUnit.unit).1 := hg
      rw [hg']
      field_simp
    · have hne : (U (j PUnit.unit) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2⟩
      have hv' : valF M.pt (U (j PUnit.unit)) ((t i).f (j PUnit.unit)) = v i / v (j PUnit.unit).1 :=
        ht i (j PUnit.unit) hne
      refine ev_injective _ (hW j) ?_
      simp only [map_mul, hτ]
      rw [ev_appLE, ev_resG_top]
      change _ = v i * ev _ (hW j) (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹))
      rw [ev_resG_top, hv', div_eq_mul_inv]

end GlobalTheory.TupleBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ), EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  first | exact @GlobalTheory.PolDeg.rescale_psiEven | exact GlobalTheory.PolDeg.rescale_psiEven | (intros; apply GlobalTheory.PolDeg.rescale_psiEven <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.QuadIff

variable {R : Type} [CommRing R] [IsDomain R]

def germU (z : (TK R).left) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)

theorem germU_injective (z : (TK R).left) : Function.Injective (germU z) := by
  let ev : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have e : ∀ k : (FractionRing R)ˣ, (germU z k).val = ev k.val := fun k =>
    (gs_unit (𝟙 (TK R).left) z ⊤ trivial (unitOn k)).symm.trans ((gs_eq _ z ⊤ trivial _).trans rfl)
  intro a b h
  exact Units.ext (ev.injective ((e a).symm.trans ((congrArg Units.val h).trans (e b))))

theorem exists_good_pt (D : DegPre R) : ∃ (z : (TK R).left) (J : _), Good D.P.L z J := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun χ : (TK R).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  exact ⟨z, J, hJ⟩

theorem even_iff (D : DegPre R) : D.PsiEven ↔ ∀ (χ : D.X) z J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val (LB.pullGen D.P.L _ _ D.sym (D.xK χ)) (𝟙 _) z J = val (D.psi χ) (𝟙 _) z J :=
  ⟨fun h χ _ _ hJ => (val_mul hJ _ _ _).symm.trans (val_corr hJ (h χ) (𝟙 _)),
    fun h χ => corr_of_val D.P.isLB fun y J hJ => (val_mul hJ _ _ _).trans (h χ y J hJ)⟩

theorem bimult_iff (D : DegPre R) : D.TauBimult ↔ ∀ (a a' b : D.X) z J, Good D.P.L z J →
    val (D.tau (a + a') b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J :=
  ⟨fun h a a' b _ _ hJ => (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _)),
    fun h a a' b => corr_of_val D.P.isLB fun y J hJ =>
      (val_mul hJ _ _ _).trans ((h a a' b y J hJ).trans (val_mul hJ _ _ _).symm)⟩

theorem val_tau_eq (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (χ : D.X) : val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      germU z (g χ) * val (D.psi χ) (𝟙 (TK R).left) z J :=
  GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ

theorem val_tau_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val ((rescale D g).tau a b) (𝟙 (TK R).left) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * val (D.tau a b) (𝟙 (TK R).left) z J := by
  have key : ∀ (A B C p q r s : ((TK R).left.presheaf.stalk z)ˣ),
      A * p * (B * q)⁻¹ * (C * r)⁻¹ * s = A * B⁻¹ * C⁻¹ * (p * q⁻¹ * r⁻¹ * s) := fun A B C p q r s => by
    simp only [_root_.mul_inv]
    ac_rfl
  refine (val_tau_eq (rescale D g) hJ a b).trans (Eq.trans ?_ (congrArg (_ * ·) (val_tau_eq D hJ a b)).symm)
  refine Eq.trans ?_ (key _ _ _ _ _ _ _)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (val_psi_rescale D g hJ (a + b))
    (congrArg (·⁻¹) (val_psi_rescale D g hJ a))) (congrArg (·⁻¹) (val_psi_rescale D g hJ b))) rfl

theorem alg_even {G : Type*} [CommGroup G] {A B m s p : G} (h : m * s = p) : A * m * s = B * p ↔ A = B := by
  rw [_root_.mul_assoc, h, mul_left_inj]

theorem alg_cube {G : Type*} [CommGroup G] {S P A A' B Q Q' t c u v : G} (h : t * c = u * v) :
    S * P⁻¹ * B⁻¹ * t * c = Q * A⁻¹ * B⁻¹ * u * (Q' * A'⁻¹ * B⁻¹ * v) ↔ S * A * A' * B = P * Q * Q' := by
  have a := congrArg Additive.ofMul h
  constructor <;> intro e <;> apply Additive.ofMul.injective <;> have b := congrArg Additive.ofMul e <;>
    simp only [ofMul_mul, ofMul_inv] at a b ⊢
  · linear_combination (norm := abel) b - a
  · linear_combination (norm := abel) b + a

theorem even_at (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (h : D.PsiEven) (χ : D.X) {z : (TK R).left} {J}
    (hJ : Good D.P.L z J) :
    val ((rescale D g).psi (-χ : D.X)) (𝟙 _) z J * val (LB.pullGen D.P.L _ _ D.sym (D.xK χ)) (𝟙 _) z J =
      val ((rescale D g).psi χ) (𝟙 _) z J ↔ g (-χ) = g χ := by
  rw [val_psi_rescale D g hJ, val_psi_rescale D g hJ, alg_even ((even_iff D).1 h χ z J hJ)]
  exact (germU_injective z).eq_iff

theorem bimult_at (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (h : D.TauBimult) (a a' b : D.X) {z : (TK R).left} {J}
    (hJ : Good D.P.L z J) :
    val ((rescale D g).tau (a + a' : D.X) b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val ((rescale D g).tau a b) (𝟙 _) z J * val ((rescale D g).tau a' b) (𝟙 _) z J ↔
      g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b) := by
  rw [val_tau_rescale D g hJ, val_tau_rescale D g hJ, val_tau_rescale D g hJ,
    alg_cube ((bimult_iff D).1 h a a' b z J hJ)]
  simp only [← map_mul]
  exact (germU_injective z).eq_iff

theorem rescale_even_bimult_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ),
    (D.PsiEven → ((GlobalTheory.PolDeg.rescale D g).PsiEven ↔ ∀ a : D.X, g (-a) = g a)) ∧
    (D.TauBimult → ((GlobalTheory.PolDeg.rescale D g).TauBimult ↔
      (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)))) := by
  intro R _ _ D g
  obtain ⟨z, J, hJ⟩ := exists_good_pt D
  refine ⟨fun h => ⟨fun H a => ?_, fun H => ?_⟩, fun h => ⟨fun H a a' b => ?_, fun H => ?_⟩⟩
  · exact (even_at D g h a hJ).1 ((even_iff (rescale D g)).1 H a z J hJ)
  · exact (even_iff (rescale D g)).2 fun χ _ _ hJ' => (even_at D g h χ hJ').2 (H χ)
  · exact (bimult_at D g h a a' b hJ).1 ((bimult_iff (rescale D g)).1 H a a' b z J hJ)
  · exact (bimult_iff (rescale D g)).2 fun a a' b _ _ hJ' => (bimult_at D g h a a' b hJ').2 (H a a' b)

end GlobalTheory.PolDeg.QuadIff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull1Bijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisO

theorem restrict_bijective_one : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type)
    [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  intro R _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := BasisExt.hcov_of_basis s G h1
  have hdir := BasisExt.hdir_of_basis s G h2
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

end GlobalTheory.Obs.BasisO
end
end

