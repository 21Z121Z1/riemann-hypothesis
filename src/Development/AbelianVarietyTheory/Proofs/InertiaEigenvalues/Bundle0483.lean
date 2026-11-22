import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open ReciprocityTheory.ChartRestriction.G.DVR (HasVal GenHasVal wchart_le_preimage)

noncomputable section

namespace GlobalTheory.QValPull

theorem chart_eq_of_val {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {φ : PUnit → (Spec (CommRingCat.of V) ⟶ X)} {φ' : PUnit → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ : ∀ k, φ' k = jK V ≫ φ k) {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (h : ∀ (z : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ X) → L.ι),
      Good L z J → (val t (𝟙 _) z J).val =
        gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) * (val e (𝟙 _ ≫ jK V) z J).val)
    (j : PUnit → L.ι) :
    (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val := by
  apply fn_ext
  intro x hx
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL x φ' j (fun a b _ => by cases a; cases b; rfl)
    (fun k => LB.wchart_le L φ' j k hx)
  have h1 : ∀ k, J (𝟙 _ ≫ φ' k) = j k := fun k => by rw [Category.id_comp]; exact hJj k
  have h2 : ∀ k, J ((𝟙 _ ≫ jK V) ≫ φ k) = j k := fun k => by rw [Category.id_comp, ← hφ]; exact hJj k
  have eL : gs (𝟙 _) x _ (t.s j).val = (val t (𝟙 _) x J).val :=
    (gs_unit _ x _ hx _).trans (congrArg Units.val (val_of t (𝟙 _) x J j h1).symm)
  rw [eL, h x J hJ]
  refine Eq.trans ?_ (gs_mul _ x _ hx _ _).symm
  congr 1
  · exact (gs_res _ x _ hx _).symm
  · have hx' : x ∈ LB.wchart L φ' j := hx
    have hxe : x ∈ jK V ⁻¹ᵁ LB.wchart L φ j := wchart_le_preimage L (jK V) φ φ' hφ j hx'
    unfold res pullU
    simp only [Units.coe_map, MonoidHom.coe_coe]
    refine Eq.symm ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 _) (jK V) x _ hxe _).trans
      ((gs_unit (𝟙 _ ≫ jK V) x _ hxe _).trans ?_)))
    exact congrArg Units.val (val_of e _ x J j h2).symm

theorem hasVal_fracMap {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] {g : V →+* V'}
    (hg : Function.Injective g) {ϖ : V} {ϖ' : V'} {e : ℕ} (ha : Associated (g ϖ) (ϖ' ^ e))
    {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) : HasVal ϖ' (ArcPull.fracMap hg c) (e * n) := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, hv⟩ := ha
  refine ⟨v⁻¹ ^ n * Units.map (g : V →* V') u, ?_⟩
  have hϖ : g ϖ = ϖ' ^ e * ((v⁻¹ : V'ˣ) : V') := by
    rw [← hv, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have key : ∀ (w : V'ˣ) (m : ℤ), algebraMap V' (FractionRing V') ((w ^ m : V'ˣ) : V') =
      algebraMap V' (FractionRing V') (w : V') ^ m := by
    intro w m
    have h1 := Units.coe_map (algebraMap V' (FractionRing V') : V' →* FractionRing V') (w ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    simpa only [MonoidHom.coe_coe] using h1.symm
  rw [map_mul, map_zpow₀, ArcPull.fracMap_algebraMap, ArcPull.fracMap_algebraMap, hϖ, Units.val_mul, map_mul,
    map_mul, map_pow, key, mul_zpow, ← zpow_natCast, ← zpow_mul]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem gs_scal_spMap {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (z : Spec (CommRingCat.of K')) (c : K) :
    gs (spMap f) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K))) c) =
      gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K'))) (f c)) := by
  unfold gs scal spMap
  simp only [TopologicalSpace.Opens.mem_top, ↓reduceDIte]
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hn]
  rfl

theorem qVal_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    {g : V →+* V'} {D : DegPre V} {D' : DegPre V'} (hD : IsPullDeg g D D') {ϖ : V} {ϖ' : V'} {e : ℕ}
    (hg : Function.Injective g) (ha : Associated (g ϖ) (ϖ' ^ e)) (y : D'.X) (n : ℤ) (h : QVal D ϖ (hD.xe y) n) :
    QVal D' ϖ' y (e * n) := by
  obtain ⟨e0, he0, c0, hc0, hch⟩ := h
  obtain ⟨e', he', hdown⟩ := ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (spMap g)
    (fun _ : PUnit => hD.c_pr y) e0 he0
  refine ⟨e', he', ArcPull.fracMap hg c0, hasVal_fracMap hg ha hc0, ?_⟩
  refine chart_eq_of_val D'.P.isLB (fun _ => DVR.QForm.ptK_eq D' y) ?_
  intro z J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB z (fun k : Empty => k.elim) (fun k : Empty => k.elim)
    (fun a => a.elim) (fun k => k.elim)
  have hv := DVR.SectionScalarValuation.val_genHasVal (hφ := fun _ => DVR.QForm.ptK_eq D (hD.xe y)) hch (ArcPull.genMap hg) z hJ
  have hp := ArcPull.psi_val hD (ArcPull.genMap hg) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) (ArcPull.fracMap_sq hg) hJ hJ' y
  have hd := hdown _ (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J J' hJ hJ'
  have hr : ArcPull.genMap hg ≫ jK V = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ spMap g := by
    rw [← ArcPull.fracMap_sq hg, Category.assoc]
    rfl
  have hxk : (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ (D'.c y).left := by
    rw [Category.assoc]
    exact congrArg _ (DVR.QForm.ptK_eq D' y)
  rw [hp, hr, hd] at hv
  simp only [Fintype.prod_unique, zpow_neg, zpow_one] at hv
  rw [← hxk, show ArcPull.genMap hg = spMap (ArcPull.fracMap hg) from rfl, gs_scal_spMap] at hv
  generalize ArcPull.om hD.w z J J' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = o at hv
  generalize val (D'.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z J' = A at hv ⊢
  generalize val e' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J' = E at hv ⊢
  generalize gs (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z ⊤ (scal (𝟙 _) (ArcPull.fracMap hg c0)) = G at hv ⊢
  rw [Units.val_mul, Units.val_mul] at hv
  linear_combination o.val * hv + (G * E.val - A.val) * Units.mul_inv o

theorem main : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D')
    (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' →
    Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  intro T T' g D D' hD ϖ ϖ' e hg _ _ ha y n h
  exact qVal_pull hD hg ha y n h

end GlobalTheory.QValPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBlochKatoLatticeDualOrthogonal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResOrth

theorem mem_of_mk_mem_span {k Z : Type} [CommRing k] [AddCommGroup Z] [Module k Z] {A B : Submodule k Z} (hB : B ≤ A)
    {S : Set (Z ⧸ B)} (hS : ∀ ξ ∈ S, ∃ z ∈ A, ξ = Submodule.Quotient.mk z) {x : Z}
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) : x ∈ A := by
  have h1 : Submodule.span k S ≤ A.map B.mkQ := Submodule.span_le.2 fun ξ hξ => by
    obtain ⟨z, hz, rfl⟩ := hS ξ hξ
    exact ⟨z, hz, rfl⟩
  obtain ⟨z, hz, e⟩ := h1 hx
  have h2 : z - x ∈ B := (Submodule.Quotient.eq B).1 e
  simpa using A.sub_mem hz (hB h2)

section General

variable {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
  [Module k M'] (χ : Γ → k) (ρ : Representation k Γ M) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k)

def leftPerp (y : Γ → M') : Submodule k (Γ → M) where
  carrier := {x | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro x x' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add, LinearMap.add_apply, e, e']
    ring
  smul_mem' := by
    rintro c x ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    ring

def rightPerp (x : Γ → M) : Submodule k (Γ → M') where
  carrier := {y | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro y y' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add, e, e']
    ring
  smul_mem' := by
    rintro c y ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, e, smul_eq_mul]
    ring

variable [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousConstSMul k M] [ContinuousConstSMul k M']

variable {χ ρ ρ' P}

theorem cupCob_of_left_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) {x : Γ → M} (hx : x ∈ B1 ρ)
    {y : Γ → M'} (hy : y ∈ Z1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  refine ⟨fun g => P m (y g), ((IsLocallyConstant.iff_continuous _).2 hy.1).comp _, fun g h => ?_⟩
  simp only [hm, hy.2, map_sub, map_add, LinearMap.sub_apply, hP]
  ring

theorem cupCob_of_right_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {x : Γ → M} (hx : x ∈ Z1 ρ) {y : Γ → M'} (hy : y ∈ B1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  have h1 : Continuous fun g => ρ' g m := hρ'.comp (f := fun g : Γ => (g, m)) (by fun_prop)
  refine ⟨fun g => -P (x g) (ρ' g m), (((IsLocallyConstant.iff_continuous _).2 hx.1).prodMk
    ((IsLocallyConstant.iff_continuous _).2 h1)).comp fun p => -P p.1 p.2, fun g h => ?_⟩
  simp only [hm, hx.2, map_sub, map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hP]
  ring

theorem cupCob_of_span (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {S : Set (H1 ρ)} {S' : Set (H1 ρ')} (p : Z1 ρ → Prop) (p' : Z1 ρ' → Prop)
    (hS : ∀ ξ ∈ S, ∃ z, p z ∧ ξ = Submodule.Quotient.mk z) (hS' : ∀ ξ ∈ S', ∃ z, p' z ∧ ξ = Submodule.Quotient.mk z)
    (h : ∀ z z', p z → p' z' → CupCob χ ρ' P z.1 z'.1) (x : Z1 ρ) (y : Z1 ρ')
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) (hy : Submodule.Quotient.mk y ∈ Submodule.span k S') :
    CupCob χ ρ' P x.1 y.1 := by
  refine mem_of_mk_mem_span (A := (leftPerp χ ρ' P y.1).comap (Z1 ρ).subtype)
    (fun z hz => cupCob_of_left_coboundary hP hz y.2) (fun ξ hξ => ?_) hx
  obtain ⟨z, hz, rfl⟩ := hS ξ hξ
  refine ⟨z, ?_, rfl⟩
  refine mem_of_mk_mem_span (A := (rightPerp χ ρ' P z.1).comap (Z1 ρ').subtype)
    (fun z' hz' => cupCob_of_right_coboundary hP hρ' z.2 hz') (fun ξ' hξ' => ?_) hy
  obtain ⟨z', hz', rfl⟩ := hS' ξ' hξ'
  exact ⟨z', h z z' hz hz', rfl⟩

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_residue_embedding {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ f : IsLocalRing.ResidueField O →ₗ[O] KmodO O, Function.Injective f ∧ ∀ a : O,
      f (IsLocalRing.residue O a) =
        Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by simpa using hϖ.ne_zero
  let φ : O →ₗ[O] KmodO O := (Submodule.mkQ _).comp
    ((LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹).comp (Algebra.linearMap O (FractionRing O)))
  have hk : LinearMap.ker φ = IsLocalRing.maximalIdeal O := by
    ext a
    rw [LinearMap.mem_ker, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
      have hb' : algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a := hb
      rw [map_mul, hb', mul_inv_cancel_left₀ h0]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      change algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) (ϖ * b)
      rw [map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨(IsLocalRing.maximalIdeal O).liftQ φ hk.ge,
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hk.le), fun a => rfl⟩

theorem kmod_torsion {l : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (b : KmodO O) :
    ∃ n : ℕ, l ^ n • b = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hn.dvd.trans (pow_dvd_pow_of_dvd hl n)
  refine ⟨n, ?_⟩
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨c * x, ?_⟩
  have h1 : algebraMap O (FractionRing O) y ≠ 0 := by simpa using hy0
  rw [Algebra.linearMap_apply, nsmul_eq_mul, Nat.cast_pow, ← map_natCast (algebraMap O (FractionRing O)), ← map_pow,
    hc, map_mul, map_mul]
  field_simp

end DVR

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {K : Type} [Field K] [Algebra (X.O0 i) K]

theorem red_apply (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (m : Fin D.R.r → K) :
    red i K ρ g m = ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem red_dot (s : X.Sig i) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (g : GE N)
    (x y : Fin D.R.r → K) :
    red i K (Tgl i s) g x ⬝ᵥ red i K ρ g y = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (x ⬝ᵥ y) := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  have e : (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]
  rw [red_apply, red_apply, hρ, Tgl_coe, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.transpose_map, ← Matrix.map_mul, e, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero _),
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem bkOn_orthogonal : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1 := by
  intro hT D N X bkP i s hG K _ _ _ _ hK ρ hρ v hv x y hx hy
  have hloc : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hK a hn)⟩
  have hc : ContAction (red i K ρ) := by
    refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun x hx => ?_⟩
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
      rw [hx, zero_smul]
  rw [bkOn, dif_pos hv] at hx hy
  refine cupCob_of_span (ρ := (red i K (Tgl i s)).comp (DecV N v).subtype)
    (ρ' := (red i K ρ).comp (DecV N v).subtype) (P := dotProductBilin K K) (fun g a b => red_dot s hρ g.1 a b)
    (hc.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop))
    (fun z => ∃ d b, IsFCoc bkP i v hv (Tgl i s) d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b)
    (fun z => ∃ d b, IsFCoc bkP i v hv ρ d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b) ?_ ?_ ?_ x y hx hy
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  rintro z z' ⟨d, b, hd, e⟩ ⟨d', b', hd', e'⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal (X.O0 i) : Ideal (X.O0 i)) : Set (X.O0 i)) := by
    simpa using (isAdic_iff.1 (X.twistBaseCoefficientRing_isAdic i)).1 1
  have hlc : ∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (d' g a) := fun a => by
    have hca : Continuous fun g => d' g a := (continuous_apply a).comp hd'.continuous
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(hopen.preimage (hca.sub (continuous_const (y := d' g a)))).mem_nhds (x := g) (by simp)] with h hh
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hh
  obtain ⟨f, hf, ef⟩ := (GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice D N X bkP i s hG ρ hρ v hv ϖ hϖ d' hlc (fun g h a => by
    rw [hd'.cocycle, hρ]; simp)).1 ⟨d', hd', fun g a => by simp⟩ d hd
  obtain ⟨ι, hι, eι⟩ := exists_residue_embedding hϖ
  have := X.twistBaseCoefficientRing_residueField_finite i
  obtain ⟨c, hc, ec⟩ := GlobalTheory.LocalH2Injective.h2_inj hT D.host.E N.Om (X.l i) _ v (N.plOm.2 v) (X.O0 i) _ _ ι hι
    (kmod_torsion (GlobalTheory.PrimeToInertia.l_mem i))
    (fun g h => IsLocalRing.residue (X.O0 i) (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h))) f hf
    (fun g h => (eι _).trans (ef g h))
  let π : IsLocalRing.ResidueField (X.O0 i) →+* K := IsLocalRing.ResidueField.lift (algebraMap (X.O0 i) K)
  have hπ : ∀ a, π (IsLocalRing.residue (X.O0 i) a) = algebraMap (X.O0 i) K a := fun a => rfl
  refine ⟨fun g => b * b' * π (c g), hc.comp fun t => b * b' * π t, fun g h => ?_⟩
  have e1 := congrArg π (ec g h)
  rw [hπ, map_add, map_sub, Algebra.smul_def, map_mul] at e1
  have e2 : π (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i)
      ((cycZ D.host.E N.Om (X.l i) g.1 : ℤ_[X.l i]ˣ) : ℤ_[X.l i]))) =
      algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) := rfl
  rw [e2] at e1
  have e3 : z.1 g ⬝ᵥ red i K ρ g.1 (z'.1 h) =
      b * b' * algebraMap (X.O0 i) K (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h)) := by
    rw [red_apply, hρ]
    simp only [dotProduct, Matrix.mulVec, e, e', map_sum, map_mul, Matrix.map_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine e3.trans ?_
  rw [e1]
  ring

end GlobalTheory.ResOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepSpansMatrixAlgebraOfGoodPoint
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint : ∀ D : D7, ResidualIrreducibleRankR D → ResidualAbsIrreducible (D := D) := by
  intro D hN9
  have hr2 : 2 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  refine ⟨hr2, ?_⟩
  intro i hi rb hrb
  have hirr := (hN9 i hi rb hrb).1
  have habs := GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) (by omega) rb
    fun W hW => hirr W fun g _ x hx => hW g x hx
  exact GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub rb habs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedRestrict

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.T.ratio_invariant_in_K0 l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  have e : ∀ z, (P.PD K).actB ⟨g, hg⟩ z = P.actQ g z := fun z => P.PD_actB K ⟨g, hg⟩ z
  rw [e, e] at h1
  rw [mul_comm, h1, mul_comm]

variable {K K' LL : FinExt l} (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem dcris_le : Dcris (P.PD K) ρ ≤ Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  refine le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)
  have e : actVB (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) =
      actVB (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g := by
    unfold actVB
    congr 1
    exact LinearMap.ext fun z => (P.PD_actB K _ z).trans (P.PD_actB K' g z).symm
  rw [e]

theorem ddR_le : DdR (P.PD K) ρ ≤ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  refine le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)
  have e : actVdR (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) =
      actVdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g := by
    unfold actVdR
    congr 1
    exact LinearMap.ext fun z => (P.PD_actdR K _ z).trans (P.PD_actdR K' g z).symm
  rw [e]

variable [FiniteDimensional ↥LL.1 V]

theorem isCrys_restrict (T : LocTied l P AI) (hc : IsCrys (P.PD K) ρ) :
    IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨h1, -⟩ := finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ
  obtain ⟨h2, h3⟩ := finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))
  rw [isCrys_iff_finrank] at hc ⊢
  refine le_antisymm h3 ?_
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hc
  have hB := indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent
  let d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
    fun i => ⟨e i, dcris_le h ρ (e i).2⟩
  have hd : LinearIndependent ↥(K0 K') d :=
    LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype
      (hB.restrict_scalars' ↥(K0 K'))
  simpa using hd.fintype_card_le_finrank

theorem isDR_restrict_iff (T : LocTied l P AI) :
    IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  constructor
  · intro hd
    have hs := (GlobalTheory.DRFil.filSpans T K LL ρ hd).spans _
    refine GlobalTheory.DRFil.isDR_of_spans T K' LL _ fun y => ?_
    obtain ⟨m, b, d, hm, e⟩ := hs y
    exact ⟨m, b, d, fun i => ddR_le h ρ (hm i), e⟩
  · intro hd
    exact GlobalTheory.DRFil.isDR_of_spans T K LL ρ (GlobalTheory.DRFil.spans_descent l P K K' LL h V ρ
      ((GlobalTheory.DRFil.filSpans T K' LL _ hd).spans _))

theorem restrict_crys_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      (IsCrys (P.PD K) ρ → IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) ∧
        (IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
  fun _ _ _ _ T _ _ _ h _ _ _ _ _ _ ρ => ⟨isCrys_restrict h ρ T, isDR_restrict_iff h ρ T⟩

end GlobalTheory.Per.TiedRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqPowFrob
section
noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => Polynomial.coeff f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
end
end

