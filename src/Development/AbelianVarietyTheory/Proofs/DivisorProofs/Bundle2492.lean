import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerNonvanishing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowSecNonzero

def oneSec {Y : Scheme.{0}} (H : LB Y) : LB.Sec (pw H ((0 : ℕ) : ℤ)) where
  f := fun _ => 1
  compat := fun k l => by
    change rs Y (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) 1 =
      (H.g k l ^ ((0 : ℕ) : ℤ)).val * rs Y (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) 1
    simp

def powSec {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (u : ℕ) : LB.Sec (pw H (u : ℤ)) :=
  Nat.rec (motive := fun u : ℕ => LB.Sec (pw H (u : ℤ))) (oneSec H)
    (fun u σ => GlobalTheory.VeryAmpleGrowth.mulPw s u σ) u

theorem powSec_f {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι) :
    ∀ u : ℕ, (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ u
  | 0 => by simp [powSec, oneSec]; rfl
  | u + 1 => by
    change s.f k * (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ (u + 1)
    rw [powSec_f s k u, pow_succ, mul_comm]

theorem exists_pw_sec_nonzero : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  intro Y D J s i x hx u
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨powSec (s i) u, TopologicalSpace.Opens.mem_iSup.2 ⟨k₀, ?_⟩⟩
  have e := powSec_f (s i) k₀ u
  change x ∈ Y.basicOpen (show Γ(Y, D.U k₀) from (powSec (s i) u).f k₀)
  rw [e]
  cases u with
  | zero =>
    rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact Y.basicOpen_le _ hk₀
  | succ n => rw [Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]; exact hk₀

end GlobalTheory.PowSecNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SecTransport

theorem main : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  intro X M L e he hM hL σ
  refine ⟨DVR.secOfIso (u := e) σ he hM hL, ?_, DVR.nonzeroLocus_secOfIso e σ he hM hL⟩
  intro p
  apply GlobalTheory.Cartier.ext_germ
  intro x hx
  set σ' := DVR.secOfIso (u := e) σ he hM hL
  have hx' : x ∈ M.U p.2 ⊓ L.U p.1 := ⟨hx.2, hx.1⟩
  have h1 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1) (σ.f p.1)) =
      (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h2 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2) (σ'.f p.2)) =
      (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h3 : (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) =
      (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) := by
    rw [← DVR.secOfIso_spec (u := e) σ he hM hL p.2 p.1]
    exact (GlobalTheory.Cartier.germ_resG (inf_le_left : M.U p.2 ⊓ L.U p.1 ≤ M.U p.2) x hx' _).symm
  have h4 : (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) =
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
        (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := by
    unfold DVR.isoCand
    rw [map_mul]
    congr 1
    exact GlobalTheory.Cartier.germ_resG (inf_le_right : M.U p.2 ⊓ L.U p.1 ≤ L.U p.1) x hx' _
  have h5 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) =
      (X.presheaf.germ _ x hx).hom ((@id (Γ(X, L.U p.1 ⊓ M.U p.2)ˣ) (e.s p) : Γ(X, L.U p.1 ⊓ M.U p.2))) :=
    GlobalTheory.Cartier.germ_resG (DVR.divLe p.2 p.1) x hx' _
  have h6 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, h1, h2, h3, h4, ← h5, ← _root_.mul_assoc, h6, _root_.one_mul]

end GlobalTheory.SecTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HenselLift

theorem exists_lift_mem_open (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (hc : IsAdicComplete (maximalIdeal R') R') (ρ : R →+* R') (U : Over (Sp R)) (hU : Smooth U.hom)
    (x₀ : Sp (ResidueField R') ⟶ U.left) (hx : x₀ ≫ U.hom = spMap ((residue R').comp ρ))
    (O : U.left.Opens) (hO : Set.range x₀ ⊆ O) :
    ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  letI := ρ.toAlgebra
  haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs
  haveI := hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R' :=
    { χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀ := by
    ext a
    exact congr($hg a)
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  · have hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y := by
      have h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          U.left.fromSpecStalk y = x₀ := by
        rw [← Spec.map_comp_assoc, hg', hχ₀]
      have h2 := congrArg (fun h => h (closedPoint (ResidueField R'))) h1
      simp only [Scheme.Hom.comp_apply] at h2
      rw [hy] at h2
      refine Eq.trans ?_ h2
      exact congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y)
        (comap_closedPoint (residue R')).symm
    rintro _ ⟨p, rfl⟩
    refine Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_
    rw [hcl]
    exact hO ⟨_, hy⟩

end GlobalTheory.HenselLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PolSemiAbModel

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem exists_model : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro W _ _ _ hW P
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  obtain ⟨W', L, _, _, _, _, _, _, _, _, hsq, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ :=
    GlobalTheory.SS.potModel_isSemiAbelian W (FractionRing W) P.A P.isAb
  have hinj : Function.Injective (algebraMap W W') := by
    have h2 : Function.Injective ((algebraMap (FractionRing W) L).comp (algebraMap W (FractionRing W))) :=
      (algebraMap (FractionRing W) L).injective.comp (IsFractionRing.injective W (FractionRing W))
    rw [← hsq] at h2
    exact Function.Injective.of_comp h2
  haveI : CharZero W' := charZero_of_injective_algebraMap hinj
  let ε : FractionRing W' ≃ₐ[W'] L := IsLocalization.algEquiv (nonZeroDivisors W') (FractionRing W') L
  let fK : FractionRing W →+* FractionRing W' := (ε.symm : L →+* FractionRing W').comp (algebraMap (FractionRing W) L)
  have hε : (ε.symm : L →+* FractionRing W').comp (algebraMap W' L) = algebraMap W' (FractionRing W') := by
    ext x; exact ε.symm.commutes x
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P fK
  haveI : IsCommMonObj G := hG.comm
  refine ⟨W', inferInstance, inferInstance, inferInstance, algebraMap W W', fK,
    (GlobalTheory.LN.cDvr_iff W').2 ⟨inferInstance, hcompl, inferInstance⟩, hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    show ε.symm (algebraMap (FractionRing W) L (algebraMap W _ a)) = _
    rw [← RingHom.comp_apply, ← hsq, RingHom.comp_apply]
    exact ε.symm.commutes _
  · let X := (Over.pullback (spMap (algebraMap W' L))).obj G
    let T := (Over.pullback (spMap (ε.symm : L →+* FractionRing W'))).obj X
    have h₁ := isGrpPullback_pullback G (jK W')
    have hTX := isGrpPullback_pullback X (spMap (ε.symm : L →+* FractionRing W'))
    have hXG := isGrpPullback_pullback G (spMap (algebraMap W' L))
    have hTG := (hTX.comp hXG).congr (by rw [spMap_comp', hε]) rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso e
    have hYP := isGrpPullback_pullback P.A (spMap (algebraMap (FractionRing W) L))
    have hTP := (hTX.comp (hXY.comp hYP)).congr (by rw [Category.id_comp, spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, inferInstance, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance⟩

end GlobalTheory.PolSemiAbModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_separable_point_of_smooth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom →
    ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k')
      (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left),
      x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  intro R _ _ U hU O hO
  obtain ⟨W, _, _, _, ε, y, hy, hyO⟩ := GlobalTheory.exists_etale_point_of_smooth U.hom R
    (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)
  let k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R)) :=
    IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))
  have hfin : FiniteDimensional (ResidueField R) k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsep : Algebra.IsSeparable (ResidueField R) k' := Algebra.IsSeparable.of_algHom _ _ k'.val
  have hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε :=
    Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩
  have hmem : ∀ w, ε w ∈ k' := fun w => hle (hs ▸ Algebra.mem_top)
  let g : W →+* k' := ε.toRingHom.codRestrict k' hmem
  refine ⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩
  · rw [Category.assoc, hy, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    change ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)
    rw [ε.commutes]
    exact IsScalarTower.algebraMap_apply R (ResidueField R) _ r
  · rintro _ ⟨z, rfl⟩
    exact hyO ⟨_, rfl⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_sharpOver_field : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] (u : Sp K ⟶ F.X), ∃ P : PolAV (Sp K), SharpOver F W P u := by
  intro g n o _ ζ F W hW K _ u
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := GlobalTheory.LowChart.siegPull F.univ u (u ≫ F.s) rfl
  have hpb : SiegPB c F.univ u := GlobalTheory.LowChart.siegPB_siegPull F.univ u _ rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ u _ rfl F.princ
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim K c.A c.ab
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := GlobalTheory.EighthPower.exists_power c.A c.ab hd 8
  have hb := GlobalTheory.EighthPower.isSymBilin hG c hc.1
  have hL : (GlobalTheory.MatrixBundle.matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  refine ⟨{ A := G, isAb := hA, g := 8 * d, smoothDim := hdim, L := GlobalTheory.MatrixBundle.matLB c.P pr W, isLB := hL
            rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb hpr, sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb hpr
            ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG _ _ 8 _ _ _ _ c G pr W hpr hu hc.1 hW.1
            ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }, c, hpb, pr, hpr, hu, ?_⟩
  exact PolBaseChange.lbIso_refl hL

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.EighthPowerLocal

open GlobalTheory.SS GlobalTheory.CechPic GlobalTheory.MatrixBundle

theorem relAmple_diag_lam {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {B : Over (Sp R)} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hlam : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  let q := Out.powIsPowGrp B 2
  have hG : IsAbelianScheme (Out.powObj B 2) := (PowGrp.powers _ _ B 2 q).2.2.2.1 hB
  let ψ : B ⟶ Out.powObj B 2 := (Out.powIsLimit B 2).lift (Fan.mk B ![𝟙 B, (𝟙 B)⁻¹])
  have hψ : ∀ u, ψ ≫ q.pr u = ![𝟙 B, (𝟙 B)⁻¹] u := fun u => (Out.powIsLimit B 2).fac _ ⟨u⟩
  have hbox : (Out.boxLB M q.pr).IsLB := LB.isLB_linComb hM _ _
  have hfin : IsFinite ψ.left := by
    have := hB.proper
    have := hG.proper
    have : IsSeparated ((q.pr 0).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated (q.pr 0).left := IsSeparated.of_comp _ B.hom
    have : IsFinite (ψ.left ≫ (q.pr 0).left) := by
      rw [← Over.comp_left, hψ]
      exact inferInstanceAs (IsFinite (𝟙 B.left))
    exact IsFinite.of_comp _ (q.pr 0).left
  have hid : IsFinite (𝟙 B : B ⟶ B).left := inferInstanceAs (IsFinite (𝟙 B.left))
  have a₁ := (relAmple_finite_pow_iso _ B _ ψ _ 1 one_pos hB hG hbox hfin).1
    (relAmple_boxLB _ _ B 2 q M hM ha)
  refine (relAmple_finite_pow_iso _ B B (𝟙 B) _ 1 one_pos hB hB (pull_isLB hbox _) hid).2.2.2 _
    (pull_isLB hlam _) ((cls_eq_iff (pull_isLB hbox _) (pull_isLB hlam _)).1 ?_) a₁
  have h₀ : pull (1 : B ⟶ B).left (cls M hM) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls M hM))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := R) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls M hM) (fst B B) (snd B B) := cls_cube_two hM _ _ hlam
  have h₂ := lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  rw [cls_pull hbox, cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd, cls_linComb hM, map_sum, Fin.sum_univ_two,
    one_smul, one_smul, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, hψ, hψ]
  refine Eq.trans ?_ (eq_neg_of_add_eq_zero_left h₂.symm).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

open SiegelOfPolarised PrimNorm in

def siegOne (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : Rˣ) : R) (𝟙 (Sp R)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact EighthPowerFactor.weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

end GlobalTheory.EighthPowerLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubringStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧ IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  first | exact @GlobalTheory.SmoothProperModel.exists_smooth_proper_model | exact GlobalTheory.SmoothProperModel.exists_smooth_proper_model | (intros; apply GlobalTheory.SmoothProperModel.exists_smooth_proper_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_morphism_basicOpen_agree_flat : ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp R) (B Z B₀ : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → QuasiCompact pB → QuasiSeparated pB → IsSeparated pZ → LocallyOfFinitePresentation pZ → ∀ (φ₀ : B₀ ⟶ B) (u₀ : B₀ ⟶ Z), Flat φ₀ → u₀ ≫ pZ = φ₀ ≫ pB → ∀ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB → (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)), t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u) → ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) → ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y), t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  first | exact @GlobalTheory.Desc.exists_spread_basicOpen_agree | exact GlobalTheory.Desc.exists_spread_basicOpen_agree | (intros; apply GlobalTheory.Desc.exists_spread_basicOpen_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValuesStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linForm_bilinForms_eq_sum_minimiser_values : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ ℓ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin 8 → Fin r → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ c, ν c * qW W b (μ c) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_qW_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_qW_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_qW_lifts <;> assumption)
end

