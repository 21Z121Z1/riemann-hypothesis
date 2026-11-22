import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TrBasis

variable {K : Type} [Field K]

theorem isAlgebraic_div_of_mem {s : Set K} {a b : K} (ha : a ∈ Algebra.adjoin ℤ s)
    (hb : b ∈ Algebra.adjoin ℤ s) (hb0 : b ≠ 0) : IsAlgebraic (Algebra.adjoin ℤ s) (a / b) := by
  refine ⟨Polynomial.C (⟨b, hb⟩ : Algebra.adjoin ℤ s) * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (Polynomial.coeff · 1) h
    simp at h1
    exact hb0 (congrArg Subtype.val h1)
  · simp [mul_div_cancel₀ _ hb0]

theorem isAlgebraic_trans [CharZero K] {s t : Set K}
    (ht : Algebra.IsAlgebraic (Algebra.adjoin ℤ t) K)
    (hts : ∀ w ∈ t, IsAlgebraic (Algebra.adjoin ℤ s) w) :
    Algebra.IsAlgebraic (Algebra.adjoin ℤ s) K := by
  rw [← AlgebraicIndependent.matroid_spanning_iff] at ht ⊢
  rw [Matroid.spanning_iff_closure_eq] at ht ⊢
  refine Set.eq_univ_of_univ_subset ?_
  rw [AlgebraicIndependent.matroid_e] at ht
  rw [← ht]
  refine Matroid.closure_subset_closure_of_subset_closure ?_
  intro w hw
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact (Subalgebra.mem_algebraicClosure _ _).2 (hts w hw)

theorem trBasis_of_integral_ratR (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1))
    (A : Subring K) (htr : Algebra.trdeg ℤ K = D) (hl : x l ≠ 0) (hA : Algebra.FiniteType ℤ A)
    (hint : ∀ w ∈ A, IsIntegral (ratR x l) w)
    (hfr : ∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) :
    (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧
      FiniteDimensional (ratF x) K := by
  haveI : FaithfulSMul ℤ K := (faithfulSMul_iff_algebraMap_injective ℤ K).mpr Int.cast_injective
  set y : Fin (D + 1) → K := fun j => x j / x l with hy
  have hle : ratR x l ≤ (Algebra.adjoin ℤ (Set.range y)).toSubring :=
    Subring.closure_le.2 Algebra.subset_adjoin
  let φ : ratR x l →+* Algebra.adjoin ℤ (Set.range y) :=
    { toFun := fun v => ⟨v, hle v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hAlgA : ∀ w ∈ (A : Set K), IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) w := fun w hw =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) (hint w hw)).isAlgebraic
  have hAlgY : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) K := by
    refine isAlgebraic_trans (t := (A : Set K)) ⟨fun w => ?_⟩ hAlgA
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hfr w
    exact isAlgebraic_div_of_mem (Algebra.subset_adjoin ha) (Algebra.subset_adjoin hb) hb0
  set z : Fin D → K := fun j => x (l.succAbove j) / x l with hz
  have hAlgZ : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range z)) K := by
    refine isAlgebraic_trans hAlgY ?_
    rintro _ ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · subst h
      simp only [hy, div_self hl]
      exact isAlgebraic_one
    · exact isAlgebraic_algebraMap (⟨z j', Algebra.subset_adjoin ⟨j', rfl⟩⟩ :
        Algebra.adjoin ℤ (Set.range z))
  have hZ : IsTranscendenceBasis ℤ z :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ z (by rw [htr]; simp)
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · exact h ▸ hl
    · intro h0
      exact hZ.1.ne_zero j' (by simp [hz, h0])
  set u : Fin D → K := fun j => x j.succ / x 0 with hu
  have hv : ∀ k, x k / x 0 ∈ Algebra.adjoin ℤ (Set.range u) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [div_self (hx 0)]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hAlgU : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range u)) K := by
    refine isAlgebraic_trans hAlgZ ?_
    rintro _ ⟨j, rfl⟩
    have e : z j = (x (l.succAbove j) / x 0) / (x l / x 0) := by
      simp only [hz]; field_simp [hx 0, hl]
    rw [e]
    exact isAlgebraic_div_of_mem (hv _) (hv _) (div_ne_zero hl (hx 0))
  have hU : IsTranscendenceBasis ℤ u :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ u (by rw [htr]; simp)
  refine ⟨hx, hU.1, ?_⟩

  have hleF : ∀ {v : K}, v ∈ Algebra.adjoin ℤ (Set.range u) → v ∈ ratF x := fun hv =>
    Algebra.adjoin_le (S := subalgebraOfSubring (ratF x).toSubring) Subfield.subset_closure hv
  let ψ : Algebra.adjoin ℤ (Set.range u) →+* ratF x :=
    { toFun := fun v => ⟨v, hleF v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hAlgF : Algebra.IsAlgebraic (ratF x) K :=
    ⟨fun w => (hAlgU.isAlgebraic w).ringHom_of_comp_eq ψ (RingHom.id K) hψ (by ext; rfl)⟩
  obtain ⟨t, ht⟩ := hA.out
  let T : Set K := (Subtype.val : A → K) '' (t : Set A)
  haveI : Finite T := (t.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional (ratF x) (IntermediateField.adjoin (ratF x) T) :=
    IntermediateField.finiteDimensional_adjoin fun w _ => (hAlgF.isAlgebraic w).isIntegral
  have hmemA : ∀ a : A, (a : K) ∈ IntermediateField.adjoin (ratF x) T := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem c hc => exact IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩
    | algebraMap n => simpa using IntermediateField.intCast_mem _ n
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | mul a b _ _ ha hb => simpa using mul_mem ha hb
  have htop : IntermediateField.adjoin (ratF x) T = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, _, rfl⟩ := hfr w
    exact div_mem (hmemA ⟨a, ha⟩) (hmemA ⟨b, hb⟩)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end GlobalTheory.HSAmp.TrBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_smul_picardClass_extends_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  first | exact @GlobalTheory.DoubleClassExtension.two_smul_extends | exact GlobalTheory.DoubleClassExtension.two_smul_extends | (intros; apply GlobalTheory.DoubleClassExtension.two_smul_extends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Transl

theorem pG_comp_lift_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ g a β hβm e hβ hab h h₁ h₂
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG I e G).left = thick R I e ≫ a.left := pullback.lift_fst _ _ _
  have hh : h = (tr ae).left := by
    apply pullback.hom_ext
    · exact h₂.trans (tr_fst hae).symm
    · exact h₁.trans (Over.w (tr ae)).symm
  subst hh
  have k₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae) (𝟙 (thickObj R I e G))
  have k₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae) = toUnit _ ≫ g.b := by
    apply Over.OverMorphism.ext
    show ((thickObj R I e G).hom ≫ ae.left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ g.b.left
    rw [Category.assoc, Category.assoc]
    exact congrArg ((thickObj R I e G).hom ≫ ·) (hab _ (Over.w ae) hae)
  have k₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U₂.gt e).pG ≫ β.hom :=
    Over.OverMorphism.ext ((Category.id_comp _).trans hβ.symm)
  have k₄ : (U₂.gt e).pG ≫ (β.hom * (toUnit _ ≫ g.b)) = ((U₂.gt e).pG ≫ β.hom) * (toUnit _ ≫ g.b) := by
    rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
  rw [k₂, k₃, _root_.mul_comm (toUnit _ ≫ g.b), ← k₄] at k₁
  exact congrArg (fun q => q.left) k₁

end GlobalTheory.MumCmp.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CmpUnif

theorem thList_smul {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x}
    {a : K} (hθ : SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ) {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (h : ThList G L ρ m x θ pt c) :
    ThList G L ρ m x θ' pt (fun b => a * c b) := by
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  refine ⟨h.1, fun b => ?_, h.2.2⟩
  rw [hfn]
  exact ThG.smul hL hθ (h.2.1 b)

theorem cmp_unif : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  intro W _ _ _ _ hW D A G _ _ hG U ρ hρ K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hd
  letI := A.isAb.comm
  obtain ⟨-, -, w, hp, -, hw, -⟩ := GlobalTheory.Ex.GenericFibre.exists_isoData W _ D A G U.toUnifPre
  have h₁ := (GlobalTheory.UMin.ThMove.hasTh₂_move _ G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen _ A.A A.L ρ (jK W) _ A.isLB hρ hp
    ⟨w, hw⟩ m m' N N' K (spMap io) d d').1 hd
  set i : W →+* K := io.comp (algebraMap W (FractionRing W)) with hi
  have hinj : Function.Injective i := io.injective.comp (IsFractionRing.injective W (FractionRing W))
  have ex : spMap io ≫ jK W = spMap i ≫ 𝟙 (Sp W) := by
    rw [Category.comp_id, hi, ← Spec.map_comp]; rfl
  rw [ex] at h₁
  obtain ⟨θ, pt, pt', hθ, hl, hl'⟩ := h₁
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr W hW D A G hG U
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G (SecAt.pull G U.LG.L σ i))
  obtain ⟨u, rfl⟩ := (fnR (spMap i ≫ 𝟙 (Sp W))).surjective r
  have hP := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m N hm hm3 hmu K i pt _ hinj (thList_smul U.LG.isLB (a := u) hr hl)
  have hP' := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m' N' hm' hm3' hmu' K i pt' _ hinj
    (thList_smul U.LG.isLB (a := u) hr hl')
  have hu : u ≠ 0 := by
    obtain ⟨-, b, hb, -⟩ := hP
    exact left_ne_zero_of_mul hb
  refine ⟨u⁻¹, inv_ne_zero hu, ?_, ?_⟩
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP'

end GlobalTheory.SiegTh.CmpUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionDivisorEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actOn_tmul_tmul' {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r a : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (a ⊗ₜ v) = (r * a) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_comp, Function.comp_apply,
    Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  change r • (rep c).baseChange R (a ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem adj_actOn_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  intro p _ D G L x v w
  induction x using TensorProduct.induction_on generalizing v w with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, MulOpposite.unop_add, hx, hy]
  | tmul r c =>
    rw [starT_tmul]
    induction v using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']
    | tmul a v₀ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add, hw, hw']
      | tmul a' w₀ =>
        rw [actOn_tmul_tmul', actOn_tmul_tmul', LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj c v₀ w₀, mul_left_comm, _root_.mul_assoc]
        rfl

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.ULift

theorem psiQ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ) (hq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))) (χ : u.D.toPre.X) : l.q χ = q χ := by
  have h := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ))
  linarith

set_option maxHeartbeats 1000000 in

theorem labels_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct yy₁ hL y h
  unfold UIsLabW at hL
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, hi, hu, hR, G, iG, α, β, hα, hβ, hLB, hm, y₀, hy₀, u, lb, j,
    hq, hyy, hcong⟩ := hL
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
    y₂, hy₂, hint₂, u₂, e, T, hpsi, hpt, hw, hfw, hbw⟩ :=
    GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup E H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G iG α β
      hα hβ hLB hm y₀ hy₀ u
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨lb₂⟩ := GlobalTheory.ZH.labels_exist hLaws hLaws2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  have hmap : (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      AddSubgroup.comap (e.trans j).toAddMonoidHom
        (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : ct.T.P.D.toPre.X →+ ct.T.P.D.toPre.X).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(e.trans j) z, by simp [map_nsmul]⟩
  refine ⟨(QuotientAddGroup.map _ _ (e.trans j).toAddMonoidHom hmap).comp lb₂.yy, ?_, ?_⟩
  · unfold UIsLabW
    refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
      y₂, hy₂, u₂, lb₂, e.trans j, ?_, ?_, ?_⟩
    · intro χ
      rw [psiQ u₂ lb₂ (fun χ => lb.q (e χ)) (fun χ => hpsi χ _ (lb.q_eq (e χ))) χ]
      exact hq (e χ)
    · intro a χ hχ
      rw [AddMonoidHom.comp_apply, hχ, QuotientAddGroup.map_mk]
      rfl
    · intro k a pk pk' x x' w w' hk hx hx' hwx hwx' hww
      obtain ⟨q, hqy, hq'⟩ := hfw k pk x hk hx
      obtain ⟨q', hqy', hq''⟩ := hfw k pk' x' hk hx'
      obtain ⟨v, hvα, hvβ⟩ := hw x w hwx
      obtain ⟨v', hvα', hvβ'⟩ := hw x' w' hwx'
      have hc := hcong k a q q' (T x) (T x') v v' hk hq' hq'' hvα hvα'
        (by rw [hvβ', hww, ← Category.assoc v, hvβ, Category.assoc])
      rw [hqy, hqy'] at hc
      exact hc
  · unfold UDeep.Compat
    intro a μ hμ
    have hN₁ : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
    have hr₁ : 0 < X₁.S.r := by
      obtain ⟨i, -, hi'⟩ := X₁.ρ.r_eq
      rw [hi']; exact pow_pos X₁.ρ.n_prime.pos _
    have hN₂ : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
    have hr₂ : 0 < D.X.S.r := by
      obtain ⟨i, -, hi'⟩ := D.X.ρ.r_eq
      rw [hi']; exact pow_pos D.X.ρ.n_prime.pos _
    have hk1 : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos hr₁ hN₁
    have hk2 : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos hr₂ hN₂
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact Dvd.dvd.mul_left (D.dvd.trans (dvd_pow_self _ two_ne_zero)) _
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) = D.X.S.r * D.X.S.N :=
      Nat.div_mul_cancel hdvd
    have hd1 : 1 ≤ D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) := Nat.div_pos (Nat.le_of_dvd hk2 hdvd) hk1
    obtain ⟨pk₀, x₀, hx₀, hx₀φ⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest _ _ _ ρ' p y₀ u a
    have h1 : lb.yy a = QuotientAddGroup.mk pk₀.y := lb.yy_eq a pk₀ x₀ hx₀ hx₀φ
    have h2 := hyy a pk₀.y h1
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.QLevelRescale.exists_qkPt_rescale _ _ _ ρ' p y₀ u (X₁.S.r * X₁.S.N)
      (D.X.S.r * D.X.S.N) (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) pk₀ x₀ hk1 hd1 hd.symm hx₀
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw _ pk' x₀ hk2 hpk'
    have hx₂ : (T.symm x₀).left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left :=
      (hpt (T.symm x₀) a).2 (by rw [Equiv.apply_symm_apply]; exact hx₀φ)
    have h3 : lb₂.yy (D.lab a) = QuotientAddGroup.mk pk₂.y := lb₂.yy_eq (D.lab a) pk₂ (T.symm x₀) hpk₂ hx₂
    rw [AddMonoidHom.comp_apply, h3, QuotientAddGroup.map_mk]
    have h4 : (e.trans j).toAddMonoidHom pk₂.y = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • j pk₀.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h4]
    rw [h2] at hμ
    rw [QuotientAddGroup.eq] at hμ ⊢
    obtain ⟨z, hz⟩ := hμ
    refine ⟨z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    calc (D.X.S.r * D.X.S.N) • z
        = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • (X₁.S.r * X₁.S.N) • z := by rw [smul_smul, hd]
      _ = _ := by rw [hz, smul_add, smul_neg]

end GlobalTheory.UPoinc.ULift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valF_spMap_comp {F F' : Type} [Field F] [Field F'] (σ : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF (spMap σ ≫ x) U f = σ (valF x U f) := by
  classical
  have h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => h (show (spMap σ).base y ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top]
  exact congrArg (fun q => q.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  classical
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {K : Type} [Field K] (k₀ : Subfield K) {X Y Y' : Scheme.{0}}

theorem valF_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : valF x U a ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hx
  have h₀ : ⊤ ≤ P₀ ⁻¹ᵁ U := (top_le_iff_mem P₀ U ((spMap k₀.subtype).base z)).2 h
  rw [valF_spMap_comp k₀.subtype P₀ U h₀ a]
  exact (valF P₀ U a).2

theorem gs_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : ∃ c ∈ k₀, gs x z U a = toStk z c :=
  ⟨valF x U a, valF_mem_of_defOver k₀ hx U z h a, (toStk_valF_gs x U z h a).symm⟩

variable {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_mem_of_defOver (t : LB.Gen (LB.LinComb L φ ε)) {r : Sp K ⟶ Y} (hr : DefOver k₀ r) (z : Sp K)
    {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) : ∃ c ∈ k₀, (val t r z J).val = toStk z c := by
  have hm := hJ.mem φ r
  obtain ⟨c, hc, e⟩ := gs_mem_of_defOver k₀ hr _ z hm (t.s fun k => J (r ≫ φ k)).val
  exact ⟨c, hc, (gs_unit r z _ hm _).symm.trans e⟩

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem spMap_subtype_cancel {R : Type} [CommRing R] {a b : Sp k₀ ⟶ Sp R}
    (h : spMap k₀.subtype ≫ a = spMap k₀.subtype ≫ b) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at h ⊢
  congr 1
  simp only [spMap, ← Spec.map_comp] at h
  have e := Spec.map_injective h
  ext y
  exact congrArg (fun q => q.hom y) e
end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem defOver_comp {X Y : Scheme.{0}} {P : Sp K ⟶ X} (hP : DefOver k₀ P) (g : X ⟶ Y) : DefOver k₀ (P ≫ g) := by
  obtain ⟨P₀, rfl⟩ := hP
  exact ⟨P₀ ≫ g, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀) : DefOver k₀ (spMap f) :=
  ⟨spMap (f.codRestrict k₀ hf), by simp only [spMap, ← Spec.map_comp]; rfl⟩

theorem defOver_pullback {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Sp R} {g : B ⟶ Sp R}
    {x : Sp K ⟶ pullback f g} (h₁ : DefOver k₀ (x ≫ pullback.fst f g)) (h₂ : DefOver k₀ (x ≫ pullback.snd f g)) :
    DefOver k₀ x := by
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hw : Q₁ ≫ f = Q₂ ≫ g := spMap_subtype_cancel k₀ (by
    rw [← Category.assoc, hQ₁, ← Category.assoc, hQ₂, Category.assoc, Category.assoc, pullback.condition])
  refine ⟨pullback.lift Q₁ Q₂ hw, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hQ₁]
  · rw [Category.assoc, pullback.lift_snd, hQ₂]

variable {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_spMap_mem {R : Type} [CommRing R] {L : LB X} {φ : Ix → (Sp R ⟶ X)} (t : LB.Gen (LB.LinComb L φ ε))
    (f : R →+* K) (hf : ∀ a, f a ∈ k₀) (z : Sp K) {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ c ∈ k₀, (val t (spMap f) z J).val = toStk z c :=
  val_mem_of_defOver k₀ t (defOver_spMap k₀ f hf) z hJ

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

end GlobalTheory.Poinc.Sep
end
end

