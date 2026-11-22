import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0107
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
section
namespace GlobalTheory.LN

open IsLocalRing

theorem isIntegral_or_isIntegral_inv (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F]
    [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (x : F) :
    IsIntegral O x ∨ IsIntegral O x⁻¹ := by
  let K := FractionRing O
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := inferInstance
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : IsDiscreteValuationRing (integralClosure O L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  let f : L →ₐ[O] F := (IntermediateField.val L).restrictScalars O
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    have h : IsIntegral O y := hz ▸ z.2
    exact h.map f
  · right
    have h : IsIntegral O y⁻¹ := hz ▸ z.2
    have h' := h.map f
    rwa [map_inv₀] at h'

theorem exists_valuationSubring_isIntegral : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  intro O _ _ _ ϖ h F _ _ _ _ _
  rcases h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩
  · refine ⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    have ha : IsAlgebraic O x :=
      (IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    letI := hF.toField
    exact ha.isIntegral
  · haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc
    exact ⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩,
      fun x => Iff.rfl⟩

end GlobalTheory.LN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.ThetaLocal

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_resG {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  have : X.basicOpen (resG X h a) = V ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_basicOpen_appLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ X.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ X.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_basicOpen_mul {U : X.Opens} (a b : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (a * b) ↔ x ∈ X.basicOpen a ∧ x ∈ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem nonvanishing_of_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) (p : M.ι)
    (hp : x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) :
    ∃ q, x ∈ X.basicOpen (coord s q) := by
  have hp' := X.basicOpen_le _ hp
  obtain ⟨q, hq⟩ := exists_chart hL x
  have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
    inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
  have e' := congrArg (fun a => x ∈ X.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
  have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp', hp'.1, hq⟩
  exact ⟨q, (e'.1 ⟨hx, hp⟩).2.2⟩

theorem exists_sec_pull {L : LB X} {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) (F : Y ⟶ X) (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {O : X.Opens} (hO : ⊤ ≤ F ⁻¹ᵁ O) (θ : ∀ i, Γ(X, O ⊓ L.U i)) (hθ : θ ∈ secOn L O) :
    ∃ θ' : L'.Sec, ∀ (y : Y) (i : L.ι), F y ∈ X.basicOpen (θ i) → ∃ k, y ∈ Y.basicOpen (θ'.f k) := by
  have hP : (L.pull F).IsLB := Semi.LB.isLB_pull hL F
  let e := isoOfGen hL' hP w hw
  let s : Γ(toMod (L.pull F), F ⁻¹ᵁ O) := pullSec L F O (mkSec θ hθ)
  let s' : Γ(toMod L', F ⁻¹ᵁ O) := e.inv.app _ s
  have hs : e.hom.app _ s' = s := by
    have := congrArg (fun q => q.app (F ⁻¹ᵁ O) s) e.inv_hom_id
    exact this
  refine ⟨globalEquiv L' ((toMod L').presheaf.map (homOfLE hO).op s'), fun y i hy => ?_⟩
  obtain ⟨k, hk⟩ := nonvanishing_of_iso hL' hP w hw s' y (fun _ => i) (by
    change y ∈ Y.basicOpen (coord (e.hom.app _ s') _)
    rw [hs]
    exact (mem_basicOpen_appLE F (pull_inf_le F O (fun _ => i)) (θ i) y).2
      ⟨⟨(X.basicOpen_le _ hy).1, mem_pull.2 (X.basicOpen_le _ hy).2⟩, hy⟩)
  refine ⟨k, ?_⟩
  rw [globalEquiv_f, coord_map, mem_basicOpen_resG, mem_basicOpen_resG]
  have := (Y.basicOpen_le _ hk).2
  exact ⟨this, ⟨trivial, this⟩, hk⟩

theorem thetaNZ_of_pushInvertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H S t₀ h R _ _ ξ t m
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h (ξ (IsLocalRing.closedPoint R))
  have hall : ∀ y : Sp R, ξ y ∈ V := fun y =>
    ((IsLocalRing.specializes_closedPoint y).map ξ.continuous).mem_open V.isOpen hV
  have hc : IsPullback m.cm.F t.G.hom t₀.G.hom ξ := m.cart.1
  have hpt : ∀ g : t.G.left, t₀.G.hom (m.cm.F g) = ξ (t.G.hom g) := fun g =>
    congrArg (fun q => q g) hc.w
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨θ', h'⟩ := exists_sec_pull t₀.PP.isLB t.PP.isLB m.cm.F w hw (O := t₀.G.hom ⁻¹ᵁ V)
    (fun g _ => by
      change t₀.G.hom (m.cm.F g) ∈ V
      rw [hpt]; exact hall _) θ hθ
  refine ⟨θ', fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := h2 (ξ y) (hall y)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hc g y hg
  obtain ⟨k, hk⟩ := h' z i (by rw [hz₁]; exact hi)
  exact ⟨z, k, hz₂, hk⟩

end GlobalTheory.ThetaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.FibreNonzero

def pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => ((1 : ℕ) : ℤ))) :=
  LBGerm.secOfGerm (fun j => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : Fin 1 => h) j 0)).op).hom
      ((h.app (L.U (j 0))).hom (θ.f (j 0)))) fun y i j hi hj => by
    have hi' : (𝟙 Y ≫ h) y ∈ L.U (i 0) := Set.mem_iInter.1 hi 0
    have hj' : (𝟙 Y ≫ h) y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    refine ((gs_res _ y _ hi _).trans (gs_pull (𝟙 Y) h y _ hi' _)).trans ((gs_compat θ _ y hi' hj').trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) ((gs_res _ y _ hj _).trans (gs_pull (𝟙 Y) h y _ hj' _)).symm))
    refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => h) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 Y) y i j hi hj).symm
    simp

theorem mem_nonzeroLocus_pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) (y : Y) (i : L.ι)
    (hy : h y ∈ X.basicOpen (θ.f i)) : y ∈ nonzeroLocus (pullOne θ h) := by
  have hi' : (𝟙 Y ≫ h) y ∈ L.U i := X.basicOpen_le _ hy
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => i) := Set.mem_iInter.2 fun _ => hi'
  refine (mem_nonzeroLocus_iff_isUnit (pullOne θ h) (k := fun _ => i) hi).2 ?_
  have e := (gs_res (𝟙 Y) y (LB.wchart_le L (fun _ : Fin 1 => h) (fun _ => i) 0) hi _).trans
    (gs_pull (𝟙 Y) h y _ hi' (θ.f i))
  exact e ▸ (LBGerm.isUnit_gs_iff _ y _ hi' _).2 hy

theorem isIso_snd_left {S : Scheme.{0}} (G : Over S) : IsIso (snd (𝟙_ (Over S)) G).left := by
  have : IsIso (snd (𝟙_ (Over S)) G) := by
    rw [← leftUnitor_hom]; infer_instance
  exact inferInstanceAs (IsIso ((Over.forget S).map (snd (𝟙_ (Over S)) G)))

end GlobalTheory.FibreNonzero

open GlobalTheory.FibreNonzero in

theorem GlobalTheory.fibNZ_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  intro R V _ _ _ _ I I' φ D D' A G _ _ A' G' _ _ U U' F C
  have := isIso_snd_left G
  have := isIso_snd_left G'
  refine ⟨fun ⟨θ, hθ⟩ => ⟨pullOne θ _, fun y => ?_⟩, fun k σ σ' h hσ y' => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hθ y
    obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
    refine ⟨z, ?_, mem_nonzeroLocus_pullOne θ _ z i hi⟩
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply, hg]
  · obtain ⟨z, hz, hzσ⟩ := hσ (spMap φ y')
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply] at hz
    obtain ⟨g', hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback C.pb.1 _ y' hz
    obtain ⟨z', rfl⟩ := (snd (𝟙_ _) G').left.surjective g'
    refine ⟨z', by rw [← Over.w (snd (𝟙_ _) G'), Scheme.Hom.comp_apply, hg₂], ?_⟩
    let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
    have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
    have hrz : r z' = z := by
      apply (snd (𝟙_ _) G).left.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hr, Category.id_comp, Scheme.Hom.comp_apply, hg₁]
    obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
    obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
    have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 (hrz ▸ hzσ)
    rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
    exact (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.GenericPoint

theorem exists_extend {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (g : V →+* K) : ∃ g' : F →+* K, g'.comp V.subtype = g := by
  have hinj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    by_contra h0
    have hF : IsAlgebraic ℤ (a : F) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hV : IsAlgebraic ℤ a :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 hF
    refine Ideal.comap_ne_bot_of_algebraic_mem h0 ha hV (eq_bot_iff.2 fun n hn => ?_)
    have e : (n : K) = 0 := by simpa using hn
    exact_mod_cast e
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] {U : Set (Sp R)} (hU : IsOpen U) (h : U.Nonempty)
    (q : Sp (FractionRing R)) : jK R q ∈ U := by
  obtain ⟨x, hx⟩ := h
  refine Specializes.mem_open (x := jK R q) (y := x) ?_ hU hx
  refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun a ha => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  have h1 : algebraMap R (FractionRing R) a ∈ q.asIdeal := ha
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
  rw [h1]; exact Ideal.zero_mem _

theorem lbIso_pull {W X Y : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y)
    {a' : W ⟶ X} (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ _ _ j fun _ => ha) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_of_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem polAt_of_lift {X S Z : Scheme.{0}} {T : SAB H X} {t : SAB H S} {t' : SAB H Z} {ξ : S ⟶ X} {j : Z ⟶ X}
    (m : SABMap t T ξ) (m' : SABMap t' T j) (hp : IsProper t'.G.hom) (hA : RelAmple t'.G t'.PP.L)
    (hK : KTriv t'.G t'.PP.L) {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Z) (h : y ≫ j = x ≫ ξ) : PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) T.G (x ≫ ξ) (pullback.fst t.G.hom x ≫ m.φ) :=
    (isGrpPullback_pullback t.G x).comp m.cart
  have w : (pullback.fst t.G.hom x ≫ m.φ) ≫ T.G.hom = (pullback.snd t.G.hom x ≫ y) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m'.φ = pullback.fst t.G.hom x ≫ m.φ ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ y :=
    ⟨_, m'.cart.1.lift_fst _ _ w, m'.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G y ψ :=
    m'.cart.cancel (g₁.congr h.symm h₁.symm) h₂
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (t'.PP.L.pull ψ) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB T.PP.isLB _) (pull_isLB t'.PP.isLB _)
      (lbIso_pull (lbIso_of_sabMap m) _ rfl) (lbIso_pull (lbIso_of_sabMap m') _ h₁.symm).symm
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp
  have hq := amplePt Z K y t'.G ((Over.pullback x).obj t.G) ψ g₂ t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    t'.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

end GlobalTheory.LN.GenericPoint

open GlobalTheory.LN.GenericPoint in

theorem GlobalTheory.LN.generic_point_of_meets_abLocus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y p ⟨_, _, _, ⟨U, hU, _⟩, _⟩ R _ _ _ ξ t m hne
  have hop : IsOpen (ξ ⁻¹' abLocus Y.t.G) := by
    rw [← hU]; exact U.isOpen.preimage ξ.continuous
  have := c.fin
  obtain ⟨g, hg⟩ := exists_extend (K := FractionRing R) (c.V W₀) (Spec.preimage ((jK R ≫ ξ) ≫ Y.s)).hom
  have sq : (jK R ≫ ξ) ≫ Y.s = spMap g ≫ spMap (c.V W₀).subtype := by
    rw [← Geo.Tor.spMap_comp, hg]
    exact (Spec.map_preimage _).symm
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ sq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact jK_mem hop hne q
  have hy : IsOpenImmersion.lift Y.jQ _ hr ≫ Y.j = jK R ≫ ξ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  exact ⟨⟨_, hy⟩, polAt_of_lift m Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv _ _ hy,
    Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi m.cart.1 x⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GoodReductionAdaptedBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_adapted_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  first | exact @GlobalTheory.ZH.RedGood.good_reduction | exact GlobalTheory.ZH.RedGood.good_reduction | (intros; apply GlobalTheory.ZH.RedGood.good_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

noncomputable section
namespace GlobalTheory.ZH.CombLocus

def secComb {X : Scheme.{0}} {H : LB X} {J : Type} [Fintype J] (a : J → Γ(X, ⊤)) (s : J → H.Sec) : H.Sec where
  f l := ∑ k, resG X le_top (a k) * (s k).f l
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ (U V : X.Opens) (h : V ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) (a k)) = resG X (le_top : V ≤ ⊤) (a k) := by
      intro U V h
      change (X.presheaf.map (homOfLE _).op ≫ X.presheaf.map (homOfLE h).op).hom (a k) = _
      rw [← Functor.map_comp]
      rfl
    rw [map_mul, map_mul, (s k).compat i j, e, e, mul_left_comm]

theorem exists_crd_secComb {X Y : Scheme.{0}} (h : X ⟶ Y) {H : LB Y} {J : Type} [Fintype J] (σ : J → H.Sec)
    (hcov : ⨆ k, nonzeroLocus (σ k) = ⊤) (a : J → Γ(X, ⊤)) {K : Type} [Field K] (y : Sp K ⟶ X) :
    ∃ w, Crd H σ (y ≫ h) w ∧ (⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔
      ∑ k, valR y ⊤ (a k) * w k ≠ 0) := by
  have h₀ : (y ≫ h) (IsLocalRing.closedPoint K) ∈ ⨆ k, nonzeroLocus (σ k) := by rw [hcov]; trivial
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hk₀
  have h₁ : ⊤ ≤ (y ≫ h) ⁻¹ᵁ H.U l := (CrdCalc.top_le_iff _ _).2 hl
  have h₂ : ⊤ ≤ y ⁻¹ᵁ (H.pull h).U (fun _ => l) := fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  refine ⟨fun k => valR (y ≫ h) (H.U l) ((σ k).f l), ⟨l, 1, h₁, fun k => by simp⟩, ?_⟩
  have h₃ : Crd (H.pull h) (fun _ : Unit => secComb a fun k => GlobalTheory.secPull (σ k) h) y
      (fun _ => ∑ k, valR y ⊤ (a k) * valR (y ≫ h) (H.U l) ((σ k).f l)) := by
    refine ⟨fun _ => l, 1, h₂, fun _ => ?_⟩
    rw [Units.val_one, one_mul, CrdCalc.valR_eq y _ h₂]
    refine Eq.symm ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_))
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ h₂]
    exact congrArg _ (GlobalTheory.Points.valR_appLE y h _ h₂ _)
  exact (CrdCalc.crd_isUnit_iff () h₃).symm.trans isUnit_iff_ne_zero

theorem opens_eq_of_field_points {X : Scheme.{0}} {U V : X.Opens}
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ⊤ ≤ y ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ V) : U = V := by
  have e : ∀ (p : X) (O : X.Opens), ⊤ ≤ X.fromSpecResidueField p ⁻¹ᵁ O ↔ p ∈ O := fun p O =>
    ⟨fun H => by
      have := H (Set.mem_univ (IsLocalRing.closedPoint (X.residueField p)))
      have h' : X.fromSpecResidueField p (IsLocalRing.closedPoint (X.residueField p)) ∈ O := this
      exact (Scheme.fromSpecResidueField_apply p (IsLocalRing.closedPoint (X.residueField p))) ▸ h',
    fun H s _ => by
      change X.fromSpecResidueField p s ∈ O
      rwa [Scheme.fromSpecResidueField_apply]⟩
  ext p
  exact (e p U).symm.trans ((h _ (X.fromSpecResidueField p)).trans (e p V))

theorem isAffineHom_homOfLE {P Z : Scheme.{0}} (π : P ⟶ Z) {V W : Z.Opens} (e : V ≤ W) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) : IsAffineHom (P.homOfLE (π.preimage_mono e)) := by
  have : IsAffine V := hV
  have : IsAffine W := hW
  have sq : IsPullback (P.homOfLE (π.preimage_mono e)) (π ∣_ V) (π ∣_ W) (Z.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) (v₁₃ := π) ?_ ?_ (isPullback_morphismRestrict π W).flip
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (isPullback_morphismRestrict π V).flip
    · rw [← cancel_mono W.ι]
      simp
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip (inferInstance : IsAffineHom (Z.homOfLE e))

theorem isAffineOpen_of_comb : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  intro P Z π _ J _ D W hW hD H
  have : IsAffine W := hW
  have : IsAffineHom (π.resLE W D hD) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_
    obtain ⟨W', H, σ, m, hz, hW', hcov, haff, hiff⟩ := H z.1 z.2
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := z.1) (U := W ⊓ W') ⟨z.2, hz⟩
    have hle' : V ≤ W ⊓ W' := hle
    have : IsAffine V := hV
    refine ⟨W.ι ⁻¹ᵁ V, hzV, hV.preimage_of_isOpenImmersion _ (by simpa using hle'.trans inf_le_left), ?_⟩
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
      ← D.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    have e : V ≤ W' := hle'.trans inf_le_right
    have := isAffineHom_homOfLE π e hV hW'
    set h := P.homOfLE (π.preimage_mono e) with hh
    have hι : h ≫ (π ⁻¹ᵁ W').ι = (π ⁻¹ᵁ V).ι := Scheme.homOfLE_ι _ _
    have ha : ⊤ ≤ ((π ⁻¹ᵁ V).ι ≫ π) ⁻¹ᵁ (W ⊓ W') := fun p _ => hle' p.2
    let a : J → Γ((π ⁻¹ᵁ V).toScheme, ⊤) := fun k => (((π ⁻¹ᵁ V).ι ≫ π).appLE (W ⊓ W') ⊤ ha).hom (m k)
    have ht := isAffineOpen_nonzeroLocus_of_universallyClosed (π ∣_ V) (fun k => GlobalTheory.secPull (σ k) h)
      (by simp only [GlobalTheory.nonzeroLocus_secPull]; rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
      (fun k => by rw [GlobalTheory.nonzeroLocus_secPull]; exact (haff k).preimage h)
      (secComb a fun k => GlobalTheory.secPull (σ k) h)
    have hE : nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) = (π ⁻¹ᵁ V).ι ⁻¹ᵁ D := by
      have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ V).toScheme),
          ⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔ ⊤ ≤ y ⁻¹ᵁ ((π ⁻¹ᵁ V).ι ⁻¹ᵁ D) := by
        intro K _ y
        obtain ⟨w, hw, hiff'⟩ := exists_crd_secComb h σ hcov a y
        have e₁ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι = y ≫ (π ⁻¹ᵁ V).ι := by rw [Category.assoc, hι]
        have e₂ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι ≫ π = y ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [← Category.assoc, e₁, Category.assoc]
        have h₄ := hiff K (y ≫ h) w (by rw [e₂]; exact fun p _ => (hle' (y p).2).1) hw
        rw [e₁, e₂] at h₄
        refine hiff'.trans (Iff.trans ?_ h₄.symm)
        have e₃ : ∀ k, valR y ⊤ (a k) = valR (y ≫ (π ⁻¹ᵁ V).ι ≫ π) (W ⊓ W') (m k) := fun k =>
          GlobalTheory.Points.valR_appLE y _ ha le_top _
        simp only [e₃]
      exact opens_eq_of_field_points key
    rw [hE] at ht
    have h₆ := ht.image_of_isOpenImmersion (π ⁻¹ᵁ V).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h₆
  exact isAffine_of_isAffineHom (π.resLE W D hD)

end GlobalTheory.ZH.CombLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  first | exact @GlobalTheory.ZH.FibreIndep.linearIndependent_moved | exact GlobalTheory.ZH.FibreIndep.linearIndependent_moved | (intros; apply GlobalTheory.ZH.FibreIndep.linearIndependent_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianSchemeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closureExtension_abelianScheme : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  first | exact @GlobalTheory.ZH.ClosureLifting.nonempty_ext | exact GlobalTheory.ZH.ClosureLifting.nonempty_ext | (intros; apply GlobalTheory.ZH.ClosureLifting.nonempty_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTestsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests : ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  first | exact @GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | exact GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | (intros; apply GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_generic_of_based_weightedCharts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  first | exact @GlobalTheory.ZJ.Charts.split_generic_of_based | exact GlobalTheory.ZJ.Charts.split_generic_of_based | (intros; apply GlobalTheory.ZJ.Charts.split_generic_of_based <;> assumption)
end

