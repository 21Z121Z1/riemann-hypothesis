import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldDescentAb

set_option backward.isDefEq.respectTransparency.types false

theorem fpqc_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap i) := by
  refine ⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.Flat.of_isField (Field.toIsField K₀) _

theorem isSeparated_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f)
    [IsSeparated q] : IsSeparated p := by
  have h : (MorphismProperty.diagonal @UniversallyClosed) p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf
      (show UniversallyClosed (pullback.diagonal q) from inferInstance)
  have h' : UniversallyClosed (pullback.diagonal p) := h
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩

theorem geometricallyConnected_of_isPullback {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {X Y : Scheme.{0}} {g : Y ⟶ X} {p : X ⟶ Sp K₀} {q : Y ⟶ Sp K}
    (H : IsPullback g q p (spMap i)) [hq : GeometricallyConnected q] :
    GeometricallyConnected p := by
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  obtain ⟨Ω, _, _, j, j', e⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom
  have e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext e
  have h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p
      (spMap j ≫ spMap i) := by
    rw [e']
    exact (IsPullback.of_hasPullback snd (spMap j')).paste_horiz h
  have h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst)
      (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc]))
      (pullback.snd snd (spMap j')) q (spMap j) :=
    IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H
  have hc : ConnectedSpace ↥(pullback snd (spMap j')) :=
    hq.geometrically_connectedSpace _ _ _ h₂
  have : Surjective (spMap j') := (fpqc_spMap j').1.1
  exact (pullback.fst snd (spMap j')).surjective.connectedSpace
    (pullback.fst snd (spMap j')).continuous

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (A₀ : Over S)
    (A : Over S') [GrpObj A₀] [GrpObj A] {φ : A.left ⟶ A₀.left} (H : IsGrpPullback A A₀ f φ)
    [Flat f] [Surjective f] [IsCommMonObj A] : IsCommMonObj A₀ := by
  have key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀ := by
    intro T₀ x₀ y₀
    let T : Over S' := Over.mk (pullback.snd T₀.hom f)
    let r : Over.mk (T.hom ≫ f) ⟶ T₀ :=
      Over.homMk (pullback.fst T₀.hom f) pullback.condition
    let up : (T₀ ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk
      (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f)
        (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)
    have hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ := fun x =>
      (H.1.lift_fst _ _ _).symm
    have h₁ := H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)
    have h₂ := H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)
    rw [mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul] at h₂
    have : Epi (pullback.fst T₀.hom f) := Flat.epi_of_flat_of_surjective _
    ext1
    rw [← cancel_epi (pullback.fst T₀.hom f)]
    exact h₂.symm
  constructor
  have := key _ (fst A₀ A₀) (snd A₀ A₀)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
  exact this.symm

theorem isAbelianScheme_and_relDim_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  intro K₀ K _ _ i A₀ A _ _ φ H hA
  have hf := fpqc_spMap i
  have := hf.1.1
  have := hf.1.2
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsep : IsSeparated A₀.hom := isSeparated_of_isPullback H.1 hf
  have huc : UniversallyClosed A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf
      inferInstance
  have hsm : Smooth A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance
  have h₀ : IsAbelianScheme A₀ :=
    { comm := isCommMonObj_of_isGrpPullback A₀ A H
      smooth := hsm
      proper := {}
      geomConnected := geometricallyConnected_of_isPullback i H.1 }
  refine ⟨h₀, fun g hg => ?_⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀
  have h' : SmoothOfRelativeDimension g' A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'
  obtain ⟨x, -⟩ := A.hom.surjective (Nonempty.some inferInstance)
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]
  exact hg'

end GlobalTheory.FieldDescentAb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.EmbSpan

open ReciprocityTheory.ChartRestriction.G.Out

theorem pt_pow_and_surjective (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (P : PolAV S) (f : S' ⟶ S)
    (n : ℕ) (hn : 1 ≤ n) : (∀ θ : ThetaGrp P.A P.L n (Over.mk f), θ.pt ^ n = 1) ∧
      Surjective (mulT P.A (Over.mk f) n).left := by
  obtain ⟨P', g, hg, -, hmul, hiso⟩ := hL.polBaseChange S S' f P
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨h, k, hk, -, hs, hf, -⟩ := GeomPointSections.exists_totalIso hg hmul
  let Φ : ∀ T : Over S', (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := fun T =>
    MonoidHom.mk' (toBase hg.w) (hmul T)
  have c' : (fst (baseOver S') P'.A).left = (baseOver S' ⊗ P'.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst (baseOver S') P'.A))
  let H : Over.mk ((baseOver S' ⊗ P'.A).hom ≫ f) ⟶ Over.mk f ⊗ P.A := Over.homMk h (by
    have e := Over.w (fst (Over.mk f) P.A)
    exact (congrArg (h ≫ ·) e.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ f) (hf.trans c'))))
  have Hs : H ≫ snd (Over.mk f) P.A = Φ _ (snd (baseOver S') P'.A) := Over.OverMorphism.ext hs.symm
  constructor
  · intro θ
    have sq : θ.pt.left ≫ P.A.hom = 𝟙 S' ≫ f := (Over.w θ.pt).trans (Category.id_comp f).symm
    let x' : baseOver S' ⟶ P'.A := Over.homMk (hg.lift _ _ sq) (hg.lift_snd _ _ _)
    have ex : x'.left ≫ g = θ.pt.left := hg.lift_fst _ _ _
    have e₀ : H ≫ fst (Over.mk f) P.A ≫ θ.pt = Φ _ (fst (baseOver S') P'.A ≫ x') :=
      Over.OverMorphism.ext ((Category.assoc h _ _).symm.trans ((congrArg₂ (· ≫ ·) hf ex.symm).trans
        (Category.assoc _ _ _).symm))
    have e₁ : H ≫ translPt P.A θ.pt = Φ _ (translPt P'.A x') := by
      refine (MonObj.comp_mul H (fst (Over.mk f) P.A ≫ θ.pt) (snd (Over.mk f) P.A)).trans
        (Eq.trans ?_ (map_mul (Φ _) (fst (baseOver S') P'.A ≫ x') (snd (baseOver S') P'.A)).symm)
      rw [e₀, Hs]
    have e₂ : h ≫ (translPt P.A θ.pt).left = (translPt P'.A x').left ≫ g := congrArg (fun q => q.left) e₁
    obtain ⟨t₁, h₁⟩ := KerPow.HasGen.pull (L := P.L)
      (φ := ![(snd (Over.mk f) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(n : ℤ), -n]) ⟨θ.φ, θ.isGen⟩ h
      (φ' := fun i => ![(snd (baseOver S') P'.A).left, (translPt P'.A x').left] i ≫ g)
      (fun i => by fin_cases i; exacts [hs.symm, e₂])
    obtain ⟨t₂, h₂⟩ := exists_down hw' P.isLB P'.isLB t₁ h₁
    have hx : x' ^ n = 1 := (hL.kerPow S' P' n hn _ x').1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ t₂ h₂ _⟩
    let j : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') rfl
    have ej : j ≫ θ.pt = Φ _ x' := Over.OverMorphism.ext ((Category.id_comp _).trans ex.symm)
    have : j ≫ θ.pt ^ n = j ≫ 1 := by
      rw [MonObj.comp_pow, ej, ← map_pow, hx, map_one, MonObj.comp_one]
    exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
      ((congrArg (fun q => q.left) this).trans (Category.id_comp _)))
  · have s₁ := VVRank.surjective_mulT P'.A n (hL.mulN S' P' n hn).2.2.1 (baseOver S')
    have s₂ : Surjective h := by
      have : Surjective (k ≫ h) := by rw [hk]; infer_instance
      exact Surjective.of_comp k h
    have t₁ : (mulT P.A (Over.mk f) n).left ≫ (fst (Over.mk f) P.A).left = (fst (Over.mk f) P.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₂ : (mulT P.A (Over.mk f) n).left ≫ (snd (Over.mk f) P.A).left = (snd (Over.mk f) P.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₁' : (mulT P'.A (baseOver S') n).left ≫ (fst (baseOver S') P'.A).left = (fst (baseOver S') P'.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have t₂' : (mulT P'.A (baseOver S') n).left ≫ (snd (baseOver S') P'.A).left =
        (snd (baseOver S') P'.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have e₁ : H ≫ snd (Over.mk f) P.A ^ n = Φ _ (snd (baseOver S') P'.A ^ n) := by
      rw [MonObj.comp_pow, Hs, map_pow]
    have e₂ : h ≫ (snd (Over.mk f) P.A ^ n).left = (snd (baseOver S') P'.A ^ n).left ≫ g :=
      congrArg (fun q => q.left) e₁
    have ext₁ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (Over.mk f ⊗ P.A).left},
        r ≫ (fst (Over.mk f) P.A).left = r' ≫ (fst (Over.mk f) P.A).left →
        r ≫ (snd (Over.mk f) P.A).left = r' ≫ (snd (Over.mk f) P.A).left → r = r' :=
      fun e e' => pullback.hom_ext e e'
    have e : (mulT P'.A (baseOver S') n).left ≫ h = h ≫ (mulT P.A (Over.mk f) n).left := ext₁
      (by rw [Category.assoc, Category.assoc, t₁, hf, t₁'])
      (by rw [Category.assoc, Category.assoc, t₂, ← hs, ← Category.assoc, t₂', e₂])
    have : Surjective (h ≫ (mulT P.A (Over.mk f) n).left) := by rw [← e]; infer_instance
    exact Surjective.of_comp h _

theorem exists_pow_eq {G : Type} [CommGroup G] {r N u v : ℕ} (hN : N = u * v) (hN0 : N ≠ 0) (p : Fin r → G)
    (hp : ∀ i, p i ^ N = 1) (hb : ∀ y : G, y ^ N = 1 → ∃! c : Fin r → ZMod N, ∏ i, p i ^ (c i).val = y)
    (y : G) (hy : y ^ u = 1) : ∃ a : Fin r → ZMod N, (∏ i, p i ^ (a i).val) ^ v = y := by
  have : NeZero N := ⟨hN0⟩
  have hu : u ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  obtain ⟨c, hc, -⟩ := hb y (by rw [hN, pow_mul, hy, one_pow])
  have h0 : (fun i => (((c i).val * u : ℕ) : ZMod N)) = 0 := by
    refine (hb 1 (one_pow _)).unique ?_ (by simp)
    rw [← hy, ← hc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), pow_mul]
  have hd : ∀ i, v ∣ (c i).val := fun i => by
    have := (ZMod.natCast_eq_zero_iff _ _).1 (congrFun h0 i)
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hu)
      ((dvd_of_eq (hN.trans (mul_comm u v)).symm).trans this)
  refine ⟨fun i => (((c i).val / v : ℕ) : ZMod N), ?_⟩
  rw [← hc, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), ← pow_mul, Nat.div_mul_cancel (hd i)]

theorem span_eq_top (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k : ℤ} {n : ℕ} (hk : k = n) (h4 : 4 ≤ n) (hn : (n : K) ≠ 0) {I : Type} [Nonempty I]
    (U : I → ThetaGrp P.A P.L k (Over.mk x)) (hU : ∀ y : Over.mk x ⟶ P.A, y ^ n = 1 → ∃ c, (U c).pt = y)
    (s₁ : LB.Sec (LPow P.A P.L k (Over.mk x))) (σ : I → LB.Sec (LPow P.A P.L k (Over.mk x)))
    (hσ : ∀ c, IsActOf P.A P.L k (U c) s₁ (σ c)) (h0 : (SecM.ofSec P.A s₁ : SecM P.A P.L k (Over.mk x)) ≠ 0) :
    Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L k (Over.mk x))) = ⊤ := by
  subst hk
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P n (Over.mk x)
  have e : (fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L n (Over.mk x))) =
      fun c => ρ (U c) (SecM.ofSec P.A s₁) := funext fun c => ((k₁ _ _ _).1 (hσ c)).symm
  rw [e]
  exact VVRank.span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K x n (Or.inr h4) hn) ρ k₁ k₃ k₄ U
    (fun θ => hU _ ((pt_pow_and_surjective hL P x n (by omega)).1 θ)) _ h0

theorem ne_zero_of_isGenSec (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) (th : LB.Sec (LPow P.A P.L 1 (Over.mk x))) (h : IsGenSec P.A P.L 1 th) :
    (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) ≠ 0 := by
  intro h0
  have hnt : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  have hr : Module.finrank Γ((Over.mk x).left, ⊤) (SecM P.A P.L 1 (Over.mk x)) = 1 ^ P.g :=
    (secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).1 hL.globalSectionsRank S P K x 1 le_rfl
  have z : ∀ v : SecM P.A P.L 1 (Over.mk x), v = 0 := fun v => by
    obtain ⟨r, hr⟩ := h (SecM.toSec P.A v)
    have : v = r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) := Subtype.ext (funext hr)
    rw [this, h0, smul_zero]
  have : Subsingleton (SecM P.A P.L 1 (Over.mk x)) := ⟨fun a b => (z a).trans (z b).symm⟩
  rw [Module.finrank_zero_of_subsingleton, one_pow] at hr
  exact zero_ne_one hr

theorem emb_span_eq_top : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤ := by
  rintro hL - o _ g N' J b S s t m K _ _ x σ hodd ⟨d, hd⟩ hm ⟨th, s₁, α, U, hth, -, htw, hU, hσ⟩
  have := t.ab.comm
  have hN0 : N' ≠ 0 := hodd.pos.ne'
  have hdiv : N' / m = d := by rw [hd, Nat.mul_div_cancel_left _ (by omega)]
  have hK : ((N' ^ 2 : ℕ) : K) ≠ 0 := VVRank.natCast_ne_zero (x ≫ s) (by
    simpa using b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  have hN : N' ^ 2 = m ^ 2 * d ^ 2 := by rw [hd, mul_pow]
  refine span_eq_top hL t.pol x (n := m ^ 2) (Nat.cast_pow m 2).symm (by nlinarith)
    (fun h => hK (by rw [hN, Nat.cast_mul, h, zero_mul])) U (fun y hy => ?_) s₁ σ hσ fun h0 => ?_
  · obtain ⟨a, ha⟩ := exists_pow_eq (G := (Over.mk x ⟶ t.A)) hN (pow_ne_zero _ hN0)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i)
      (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
      (fun z hz => by simpa only [linComb, List.prod_ofFn] using t.bij K x z hz) y hy
    refine ⟨a, (hU a).pt_eq.trans (Eq.trans ?_ ha)⟩
    rw [hdiv, TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
    rfl
  · have hint : IsIntegral (Over.mk x ⊗ t.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ t.A.hom t.ab.smooth
        t.ab.geomConnected).geometrically_isIntegral x _ _ (IsPullback.of_hasPullback x t.A.hom).flip
    exact ne_zero_of_isGenSec hL t.pol x th hth (VVRank.ofSec_eq_zero_of_twist t.A t.isLB
      (pt_pow_and_surjective hL t.pol x m (by omega)).2 htw h0)

end GlobalTheory.EmbSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SabMapDescent

section Bundles

variable {X Y : Scheme.{0}}

def chartPullDivPull (A B : LB X) (h : Y ⟶ X) :
    ChartPull ((LB.div B A).pull h) (LB.div (B.pull h) (A.pull h)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have b := mem_pull.1 hj'
    refine (gm_pull_g _ h (𝟙 Y) y J J' hj hj').trans ((gm_div A B (𝟙 Y ≫ h) y _ _ ⟨a, b⟩).trans (Eq.symm ?_))
    refine (gm_div (A.pull h) (B.pull h) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, ⟨mem_pull.2 b.1, mem_pull.2 b.2⟩⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g B h (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 b.1))
      (gm_pull_g A h (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 b.2))

theorem lbIso_of_gen_of_gen {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) : LBIso A B := by
  refine ⟨⟨fun p => res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
      (res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹) =
      gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
    rw [map_mul, map_inv, gm_res _ y _ hp, gm_res _ y _ hp]
  have w : ∀ {C : LB X} (c : C.Gen), c.IsGen → ∀ i j, y ∈ C.U i → y ∈ C.U j →
      gm (𝟙 X) y _ (c.s i) = gm (𝟙 X) y _ (C.g i j) * gm (𝟙 X) y _ (c.s j) := fun {C} c hc i j hi hj => by
    have hm : (𝟙 X : X ⟶ X) y ∈ C.U i ⊓ C.U j := ⟨hi, hj⟩
    have := congrArg (gm (𝟙 X) y _) (hc i j)
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at this
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [w t ht p.1 q.1 hy.1.1 hy.2.1, w s hs p.2 q.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm]

end Bundles

def IsQuot {Γ : Type} [Group Γ] {X X' : Scheme.{0}} (ρ : Γ →* Aut X) (π : X ⟶ X') : Prop :=
  IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧
    ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem IsQuot.epi {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) : Epi π :=
  ⟨fun {T} a b e => (quotient_existsUnique_comp_eq Γ X X' ρ π h T (π ≫ a)
    fun g => by rw [← Category.assoc, h.2.1 g]).unique rfl e.symm⟩

theorem IsQuot.epi_of_isPullback {X X' Y Y' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π)
    {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'} (H : IsPullback φ p p' π) (hp : Flat p') : Epi φ := by
  obtain ⟨⟨τ, hτ⟩, hall⟩ := quotient_flat_baseChange Γ X X' Y Y' ρ π φ p p' h H hp
  exact IsQuot.epi (hall τ hτ)

omit [Finite Γ] in
theorem IsQuot.isReduced {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) [IsReduced X] :
    IsReduced X' :=
  ⟨fun V => isReduced_of_injective (π.app V).hom (h.2.2 V).1⟩

theorem exists_isPullback {U U' X' P P' P₁ : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {p : P ⟶ U} {p' : P' ⟶ U'} {p₁ : P₁ ⟶ X'} [Flat p'] [Flat p₁] {φ : P ⟶ P'} {n : P ⟶ P₁}
    (hφ : IsPullback φ p p' r) (hn : IsPullback n p p₁ (r ≫ j)) (τ : Γ →* Aut P)
    (hτ : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom ∧ (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ n = n) :
    ∃ ψ : P' ⟶ P₁, φ ≫ ψ = n ∧ IsPullback ψ p' p₁ j := by
  have hφq : IsQuot τ φ := (quotient_flat_baseChange Γ U U' P P' ρ r φ p p' hq hφ inferInstance).2 τ
    fun g => ⟨(hτ g).2.1, (hτ g).1⟩
  have := hφq.epi
  obtain ⟨ψ, hψ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ φ hφq _ n fun g => (hτ g).2.2
  have w : ψ ≫ p₁ = p' ≫ j := by
    rw [← cancel_epi φ, ← Category.assoc, hψ, hn.w, ← Category.assoc, ← hφ.w, Category.assoc]
  have H := IsPullback.of_hasPullback p₁ j
  let θ : P' ⟶ pullback p₁ j := pullback.lift ψ p' w
  have h₁ : θ ≫ pullback.fst p₁ j = ψ := pullback.lift_fst _ _ _
  have h₂ : θ ≫ pullback.snd p₁ j = p' := pullback.lift_snd _ _ _
  have hκ : IsPullback (φ ≫ θ) p (pullback.snd p₁ j) r :=
    IsPullback.of_right (by rw [Category.assoc, h₁, hψ]; exact hn) (by rw [Category.assoc, h₂, hφ.w]) H
  have hκq : IsQuot τ (φ ≫ θ) := (quotient_flat_baseChange Γ U U' P _ ρ r _ p _ hq hκ inferInstance).2 τ
    fun g => ⟨by rw [← Category.assoc, (hτ g).2.1], (hτ g).1⟩
  have := hκq.epi
  obtain ⟨σ, hσ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ _ hκq _ φ fun g => (hτ g).2.1
  have : IsIso θ := ⟨σ, by rw [← cancel_epi φ, ← Category.assoc, hσ, Category.comp_id],
    by rw [← cancel_epi (φ ≫ θ), ← Category.assoc, hσ, Category.comp_id]⟩
  refine ⟨ψ, hψ, ?_⟩
  have := (IsPullback.of_horiz_isIso (fst := θ) (snd := p') (f := pullback.snd p₁ j) (g := 𝟙 U')
    ⟨by rw [h₂, Category.comp_id]⟩).paste_horiz H
  rwa [h₁, Category.id_comp] at this

theorem isGrpPullback_of_quot {U U' X' : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {G : Over U} {G' : Over U'} {G₁ : Over X'} [GrpObj G] [GrpObj G'] [GrpObj G₁] [Flat G'.hom]
    {φ : G.left ⟶ G'.left} {ψ : G'.left ⟶ G₁.left} (hφ : IsGrpPullback G G' r φ)
    (hn : IsGrpPullback G G₁ (r ≫ j) (φ ≫ ψ)) (hψ : IsPullback ψ G'.hom G₁.hom j) :
    IsGrpPullback G' G₁ j ψ := by
  have key : ∀ (T : Over U') (x y : T ⟶ G'), Flat T.hom →
      (pushPt hψ.w x * pushPt hψ.w y).left = (x * y).left ≫ ψ := by
    intro T x y hT
    have H := IsPullback.of_hasPullback T.hom r
    have := hq.epi_of_isPullback H hT
    let q := pullback.fst T.hom r
    let W : Over U := Over.mk (pullback.snd T.hom r)
    let l : (T ⟶ G') → (W ⟶ G) := fun z => Over.homMk
      (hφ.1.lift (q ≫ z.left) (pullback.snd T.hom r) (by rw [Category.assoc, Over.w z]; exact H.w))
      (hφ.1.lift_snd _ _ _)
    have hl : ∀ z, (l z).left ≫ φ = q ≫ z.left := fun z => hφ.1.lift_fst _ _ _
    let q' : Over.mk (W.hom ≫ r) ⟶ T := Over.homMk q H.w
    let q₁ : Over.mk (W.hom ≫ r ≫ j) ⟶ Over.mk (T.hom ≫ j) := Over.homMk q (by
      show q ≫ T.hom ≫ j = pullback.snd T.hom r ≫ r ≫ j
      rw [← Category.assoc, H.w, Category.assoc])
    have e₁ := hφ.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
    have e₂ := hn.2 W (l x) (l y) (q₁ ≫ pushPt hψ.w x) (q₁ ≫ pushPt hψ.w y)
      (by rw [← Category.assoc (l x).left, hl, Category.assoc]; rfl)
      (by rw [← Category.assoc (l y).left, hl, Category.assoc]; rfl)
    rw [← MonObj.comp_mul] at e₁ e₂
    rw [← Category.assoc (l x * l y).left, ← e₁] at e₂
    rw [← cancel_epi q, ← Category.assoc q]
    exact e₂
  refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
  have hf : Flat (G' ⊗ G').hom := inferInstanceAs (Flat (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have e := key (G' ⊗ G') (fst _ _) (snd _ _) hf
  let z : Over.mk (T.hom ≫ j) ⟶ Over.mk ((G' ⊗ G').hom ≫ j) := Over.homMk (lift x y).left (by
    show (lift x y).left ≫ (G' ⊗ G').hom ≫ j = T.hom ≫ j
    rw [← Category.assoc, Over.w])
  have hx' : x₀ = z ≫ pushPt hψ.w (fst _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (fst G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_fst, hx])
  have hy' : y₀ = z ≫ pushPt hψ.w (snd _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (snd G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hy])
  have hxy : x * y = lift x y ≫ (fst G' G' * snd G' G') := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hx', hy', ← MonObj.comp_mul, hxy, Over.comp_left, e, Over.comp_left, Category.assoc]
  rfl

theorem subset_abLocus {S : Scheme.{0}} (G : Over S) [IsProper G.hom] (A : Set S) : A ⊆ abLocus G :=
  fun _ _ _ _ _ _ _ => inferInstance

end SabMapDescent

open SabMapDescent in

theorem exists_sabMap_of_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ g).hom ∧ (τ g).hom ≫ ν.φ = ν.φ ∧ (τ g).hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  intro E _ _ _ H Γ _ _ U U' X' ρ r t t' t₁ τ ν j n hq hred hprop hτ
  have hq : IsQuot ρ r := hq
  have := t.semi.smooth
  have := t.semi.geomConnected
  have := t'.semi.smooth
  have := t'.semi.separated
  have := t₁.semi.smooth
  obtain ⟨ψ, hψ, hpb⟩ := exists_isPullback hq ν.cart.1 n.cart.1 τ hτ
  have hgp : IsGrpPullback t'.G t₁.G j ψ := isGrpPullback_of_quot hq ν.cart (hψ ▸ n.cart) hpb
  have := hq.epi_of_isPullback ν.cart.1 inferInstance
  obtain ⟨hint, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ U U' ρ r hq
  have : Surjective ν.cm.F := MorphismProperty.of_isPullback (P := @Surjective) ν.cart.1.flip hsurj
  have : UniversallyClosed (ν.cm.F ≫ t'.G.hom) := by rw [ν.cart.1.w]; infer_instance
  have : UniversallyClosed t'.G.hom := .of_comp_surjective ν.cm.F _
  have : IsProper t'.G.hom := {}
  have he : eSec t.G ≫ t.G.hom = 𝟙 U := Over.w η[t.G]
  have he' : eSec t'.G ≫ t'.G.hom = 𝟙 U' := Over.w η[t'.G]
  have hiso : LBIso t'.PP.L (t₁.PP.L.pull ψ) := by
    refine exists_gen_of_quotient_of_rigid Γ U U' ρ r t.G t'.G ν.cm.F (eSec t.G) (eSec t'.G)
      (LB.div (t₁.PP.L.pull ψ) t'.PP.L) hq ν.cart.1 inferInstance he he' (by rw [ν.cm.e_comm, ν.base])
      (eq_one_of_appLE_section_eq_one U t.G _ he inferInstance
        (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) ⟨hred, subset_abLocus _ _⟩)
      (LB.isLB_div (pull_isLB t₁.PP.isLB ψ) t'.PP.isLB) ?_ ?_
    · obtain ⟨c, hc⟩ := gen_chartPull (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => eSec t'.G)
        (fun _ => eSec t₁.G) (fun _ => 1) j fun _ => (cubeMapOf hgp).e_comm) t₁.PP.rig t₁.PP.rigGen
      obtain ⟨w, hw⟩ := lbIso_of_gen_of_gen t'.PP.rig t'.PP.rigGen c hc
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
    · obtain ⟨a, ha, -⟩ := ν.lin
      obtain ⟨b, hb, -⟩ := n.lin
      have hb' : LBIso t.PP.L ((t₁.PP.L.pull ψ).pull ν.cm.F) :=
        LBIso.chartPull (chartPullId _) (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => ν.cm.F)
          (fun _ => n.cm.F) (fun _ => 1) (𝟙 _) fun _ => hψ.trans (Category.id_comp _).symm) ⟨b, hb⟩
      obtain ⟨w, hw⟩ := LBIso.trans (pull_isLB t'.PP.isLB _) t.PP.isLB
        (pull_isLB (pull_isLB t₁.PP.isLB ψ) _) (LBIso.symm ⟨a, ha⟩) hb'
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X' U' t₁ t' j ψ ⟨hq.isReduced, subset_abLocus _ _⟩ hgp (fun a => by
    rw [← cancel_epi ν.cm.F, ← Category.assoc, ← ν.act, Category.assoc, hψ, n.act, ← Category.assoc, hψ]) hiso
  exact ⟨n', hn' ▸ hψ⟩

end GlobalTheory
end
end

