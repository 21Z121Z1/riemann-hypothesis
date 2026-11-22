import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_translateLevel_realBox_le_index_mul : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  first | exact @GlobalTheory.CovTop.VolBox.meas_translate_le | exact GlobalTheory.CovTop.VolBox.meas_translate_le | (intros; apply GlobalTheory.CovTop.VolBox.meas_translate_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheaf
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem mem_basicOpen_of_sub_one_mem_baseIdeal (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0})
    (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z)
    (hz : z ∈ V) (hI : I ≤ (p z).asIdeal) (hr : r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩) :
    z ∈ Z.basicOpen r := by
  have hs : z ∈ (baseIdeal p I).support := (mem_support_baseIdeal p I z).2 hI
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hz] at hs
  have h1 : z ∉ Z.basicOpen (r - 1) := by
    rw [Scheme.mem_zeroLocus_iff] at hs
    exact hs _ hr
  rw [Scheme.mem_basicOpen _ _ _ hz] at h1 ⊢
  have hsum : Z.presheaf.germ V z hz r + (-(Z.presheaf.germ V z hz (r - 1))) = 1 := by
    simp [map_sub]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact h
  · exact absurd (by simpa using h.neg) h1

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusOfIsTwistPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TranslateSection

theorem translT_inv_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    translT A z⁻¹ ≫ translT A z = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, translPt, Category.assoc, lift_snd, lift_fst, Category.id_comp, comp_lift_assoc, lift_fst_assoc]
    change (fst T A ≫ z) * ((fst T A ≫ z⁻¹) * snd T A) = snd T A
    have e : fst T A ≫ z⁻¹ = (fst T A ≫ z)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])
    rw [e, mul_inv_cancel_left]

theorem translT_surjective : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A), Function.Surjective (translT A z).left.base := by
  intro S A _ T z y
  refine ⟨(translT A z⁻¹).left.base y, ?_⟩
  have h := congrArg (fun f : T ⊗ A ⟶ T ⊗ A => f.left y) (translT_inv_comp A z)
  simpa [Scheme.Hom.comp_apply] using h

theorem mulT_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (m : ℕ) :
    mulT A (baseOver S) m = (λ_ A).hom ≫ mulA A m ≫ (λ_ A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, CartesianMonoidalCategory.leftUnitor_hom, mulT]
  refine (lift_snd _ _).trans ?_
  rw [mulA, MonObj.comp_pow, Category.comp_id]
  rfl

theorem mulT_surjective : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (m : ℕ), 1 ≤ m → Function.Surjective (mulT P.A (baseOver S) m).left.base := by
  intro S _ P m hm y
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨-, -, hs, -⟩ := hLaw.mulN S P m hm
  obtain ⟨b, hb⟩ := hs.surj ((λ_ P.A).hom.left y)
  refine ⟨(λ_ P.A).inv.left b, ?_⟩
  have h1 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left ((λ_ P.A).inv.left b)) (mulT_eq P.A m)
  have h2 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left y) (λ_ P.A).hom_inv_id
  have h3 := congrArg (fun f : P.A ⟶ P.A => f.left b) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left] at h1 h2 h3
  have h2' : (λ_ P.A).inv.left ((λ_ P.A).hom.left y) = y := h2
  have h3' : (λ_ P.A).hom.left ((λ_ P.A).inv.left b) = b := h3
  rw [h1, h3', hb, h2']

theorem mem_nonzeroLocus_of_isTwistPull : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection

end GlobalTheory.MBLow.TranslateSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CodimOne

theorem mem_preimage_sup_of_ringKrullDim_stalk_le_one :
    ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  intro X S _ f _ _ V U hV hU z hz
  by_contra hzm
  have hzU : f z ∉ U := fun h => hzm (Or.inl h)
  have hzV : z ∉ V := fun h => hzm (Or.inr h)
  set s := f z with hs

  let ξ : X := f.fiberι s (genericPoint (f.fiber s))
  have hfξ : f ξ = s := (f.range_fiberι s).le ⟨_, rfl⟩
  have hrange : ∀ y : X, f y = s → ξ ⤳ y := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hy
    exact (genericPoint_specializes w).map (f.fiberι s).continuous
  obtain ⟨x, hxV, hxs⟩ := hV s
  have hξV : ξ ∈ V := (hrange x hxs).mem_open V.isOpen hxV
  have hξz : ξ ⤳ z := hrange z rfl
  have hξnez : ξ ≠ z := fun h => hzV (h ▸ hξV)

  obtain ⟨u, huU⟩ := hU
  have hηU : genericPoint S ∈ U := (genericPoint_specializes u).mem_open U.isOpen huU
  have hηs : genericPoint S ⤳ f ξ := hfξ ▸ genericPoint_specializes s
  obtain ⟨ζ, hζξ, hfζ⟩ := (Flat.generalizingMap f) hηs
  have hζneξ : ζ ≠ ξ := by
    intro h
    apply hzU
    rw [← hfξ, ← h, hfζ]
    exact hηU
  have h1 : z < ξ := lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)
  have h2 : ξ < ζ := lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have a := Order.coheight_add_one_le h1
    have b := Order.coheight_add_one_le h2
    have : (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1 := by gcongr; exact le_add_self
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight ζ + 1 + 1 := this
      _ ≤ Order.coheight ξ + 1 := by gcongr
      _ ≤ Order.coheight z := a
  rw [ringKrullDim_stalk_eq_coheight] at hz
  have : Order.coheight z ≤ 1 := by exact_mod_cast hz
  exact absurd (hc.trans this) (by norm_num)

end GlobalTheory.CodimOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemToroidalComponentClosureOfSpecializes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option autoImplicit false

namespace GlobalTheory.CompHS

theorem exists_generisation_of_mem_closure {T : Type} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {U : Set T} (hU : IsOpen U) {y : T} (hy : y ∈ closure U) : ∃ g ∈ U, g ⤳ y := by
  haveI : NoetherianSpace (closure U) := NoetherianSpace.set _
  haveI : QuasiSober (closure U) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hd : Dense (Subtype.val ⁻¹' U : Set (closure U)) := fun z => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right subset_closure]
    exact z.2
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨y, hy⟩ : closure U)
  have hg := (isIrreducible_irreducibleComponent (x := (⟨y, hy⟩ : closure U))).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  obtain ⟨o, ho, hne, hle⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨p, hp, hpU⟩ := hd.inter_open_nonempty o ho hne
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set (closure U)) := hU.preimage continuous_subtype_val
  exact ⟨_, (hg.mem_open_set_iff hU').2 ⟨p, hle hp, hpU⟩,
    (hg.specializes mem_irreducibleComponent).map continuous_subtype_val⟩

theorem exists_generic_generisation (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, fun y hy => ?_⟩
  have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := this
  exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
    (X.fromSpecStalk x).continuous

theorem mem_barComp_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  intro E _ _ _ H Dw l Xo c Y Z x hx b hb
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := {}
  intro hcl
  have hopen := Y.j.isOpenEmbedding.isOpenMap
  have hc := (TrivOrderTieCompare.isClopen_comp Z)
  obtain ⟨w, hw, hwb⟩ := exists_generisation_of_mem_closure (hopen _ hc.compl.isOpen) hcl
  obtain ⟨ξ, hξ⟩ := exists_generic_generisation Y.X b (Y.normal b).1
  obtain ⟨u, hu, rfl⟩ := (hξ w hwb).mem_open (hopen _ hc.compl.isOpen) hw
  obtain ⟨v, hv, hv'⟩ := (hξ _ hb).mem_open (hopen _ hc.isOpen) ⟨x, hx, rfl⟩
  exact hu (Y.j.isOpenEmbedding.injective hv' ▸ hv)

end GlobalTheory.CompHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ := by
  first | exact @GlobalTheory.MBLow.TanRed.main | exact GlobalTheory.MBLow.TanRed.main | (intros; apply GlobalTheory.MBLow.TanRed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DetLine.CoverU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigSpread
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt)
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}

theorem exists_eigBasisAt {R : Type} [CommRing R] {x : Sp R ⟶ S} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
    (hx : IsUnivChart _ n xc) (χ : 𝓞 E →+* R) {m : ℕ} (B : Fin m → Fin n → R)
    (hB : ∀ i, B i ∈ ReciprocityTheory.ChartRestriction.G.Chart.eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) χ)
    (hu : ∀ v ∈ ReciprocityTheory.ChartRestriction.G.Chart.eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) χ,
      ∃! a : Fin m → R, v = ∑ j, a j • B j) :
    ∃ v : Fin m → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v := by
  refine ⟨fun i => Over.homMk (vec t x xc (B i)) (vec_tan hx _).1,
    fun i => ⟨(vec_tan hx _).2, (vec_eig_iff hx χ _).2 (hB i)⟩, fun w hw => ?_⟩
  obtain ⟨cc, hcc⟩ := vec_exists hx w.left ⟨Over.w w, hw.1⟩
  have he := (vec_eig_iff hx χ cc).1 (fun a => by rw [← hcc]; exact hw.2 a)
  refine (existsUnique_congr fun a => ?_).1 (hu cc he)
  rw [← comb_iff hx, ← hcc]
  exact exists_congr fun u => and_congr Iff.rfl
    ⟨fun h => Over.OverMorphism.ext h.symm, fun h => by rw [h]⟩

variable {l : Level H} (c : Coeff l)

theorem exists_local_basis {X : Scheme.{0}} (π : X ⟶ S) (s : X ⟶ Sp c.F) {m : ℕ} {τ : E →+* ℂ}
    (hm : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ X), y ≫ s = spMap φ →
      LieMult t.act (y ≫ π) (φ.comp (embK c τ)) m) {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L)
    (x : Sp L ⟶ X) (hφ : x ≫ s = spMap φ) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback (x ≫ π)).obj t.G}
    (hx : IsUnivChart _ n xc) (P : Matrix (Fin n) (Fin n) L)
    (hP : ∀ v, P *ᵥ v ∈ eig c φ hx τ ∧ (v ∈ eig c φ hx τ → P *ᵥ v = v)) :
    ∃ B : Fin m → Fin n → L, (∀ j, P *ᵥ B j = B j) ∧ ∀ v, ∃! a : Fin m → L, P *ᵥ v = ∑ j, a j • B j := by
  let k : Type := AlgebraicClosure (IsLocalRing.ResidueField L)
  let ψk : L →+* k := (algebraMap (IsLocalRing.ResidueField L) k).comp (IsLocalRing.residue L)
  obtain ⟨xk, hxk, hk⟩ := eig_bc c φ hx ψk
  have B : Module.Basis (Fin m) L (eig c φ hx τ) := by
    have he : IsIdempotentElem P.mulVecLin := LinearMap.ext fun v => (hP _).2 (hP v).1
    have hr : LinearMap.range P.mulVecLin = eig c φ hx τ :=
      Submodule.ext fun v => ⟨fun ⟨v', h⟩ => by rw [← h]; exact (hP v').1, fun h => ⟨v, (hP v).2 h⟩⟩
    have fr := Formalism.L2.Pj.LocFrM.range_free _ he
    have fi : Module.Finite L (LinearMap.range P.mulVecLin) := Module.Finite.range _
    rw [hr] at fr fi
    refine Module.finBasisOfFinrankEq L _ ((hk τ).2.2.trans ?_)
    have h := hm k (ψk.comp φ) (spMap ψk ≫ x)
      (by rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap])
    rw [Category.assoc] at h
    exact ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult (isGrpPullback_id t.G) (Category.comp_id _) hxk t.act t.act.act
      (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) _ (fun a => rfl)
      ((ψk.comp φ).comp (embK c τ)) h
  refine ⟨fun i => B i, fun i => (hP _).2 (B i).2, fun v => ?_⟩
  have key : ∀ a : Fin m → L, (P *ᵥ v = ∑ j, a j • (B j : Fin n → L)) ↔ B.equivFun ⟨_, (hP v).1⟩ = a := fun a => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp
  simp only [key]
  exact existsUnique_eq'

theorem exists_affine_bases {X : Scheme.{0}} (π : X ⟶ S) (s : X ⟶ Sp c.F) (m : (E →+* ℂ) → ℕ)
    (hm : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ X), y ≫ s = spMap φ →
      ∀ τ, LieMult t.act (y ≫ π) (φ.comp (embK c τ)) (m τ)) (U : X.Opens) (z : X) (hzU : z ∈ U) :
    ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : c.F →+* Γ(X, W)), z ∈ W ∧ W ≤ U ∧
      (show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ s = spMap j ∧
      ∀ τ, ∃ v : Fin (m τ) → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G),
        IsEigBasisAt t.act ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) (j.comp (embK c τ)) v := by
  obtain ⟨U₀, hU₀, hz, x₀, hx₀, C, n, xc, hx⟩ := exists_affine_chart t π z
  let j : Sp Γ(X, U₀) ⟶ X := hU₀.fromSpec
  let φ₀ : c.F →+* Γ(X, U₀) := (Spec.preimage (j ≫ s)).hom
  have hφ₀ : spMap φ₀ = j ≫ s := Spec.map_preimage _
  have hov : ∀ {R : Type} [CommRing R] (ψ : Γ(X, U₀) →+* R), (spMap ψ ≫ j) ≫ s = spMap (ψ.comp φ₀) :=
    fun ψ => by rw [Category.assoc, ← hφ₀, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨P, hP⟩ := exists_projectors c φ₀ hx
  let L : Type := X.presheaf.stalk z
  letI : Algebra Γ(X, U₀) L := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  have hloc := hU₀.isLocalization_stalk ⟨z, hz⟩
  obtain ⟨xL, hxL, hvL⟩ := vec_bc_of_chart C hx (algebraMap Γ(X, U₀) L)
    (x' := (spMap (algebraMap Γ(X, U₀) L) ≫ j) ≫ π) (by rw [hx₀, Category.assoc])
  have hPL := hP _ hxL hvL
  choose B hB hB' using fun τ =>
    exists_local_basis c π s (fun k _ _ φ y hy => hm k φ y hy τ) _ _ (hov _) hxL _ (hPL τ)
  choose g hg B₀ hB₀ using fun τ =>
    spread_basis (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl (P τ) (B τ) (hB τ) (hB' τ)
  obtain ⟨f, hfU, hzf⟩ := hU₀.exists_basicOpen_le (V := U) ⟨z, hzU⟩ hz
  let g₀ : Γ(X, U₀) := f * ∏ τ, g τ
  have hU := hU₀.basicOpen g₀
  let ρ : Γ(X, U₀) →+* Γ(X, X.basicOpen g₀) := (X.presheaf.map (homOfLE (X.basicOpen_le g₀)).op).hom
  have hρ : spMap ρ ≫ j = hU.fromSpec := hU₀.map_fromSpec hU _
  have hu : IsUnit (ρ g₀) := X.toRingedSpace.isUnit_res_basicOpen g₀
  have hx₁ : (show Sp Γ(X, X.basicOpen g₀) ⟶ X from hU.fromSpec) ≫ π = spMap ρ ≫ x₀ := by
    rw [hx₀, ← hρ, Category.assoc]
  obtain ⟨xc', hx', hv⟩ := vec_bc_of_chart C hx ρ hx₁
  have hP' := hP _ hx' hv
  refine ⟨_, hU, ρ.comp φ₀, ?_, ?_, by rw [← hρ]; exact hov ρ, fun τ => ?_⟩
  · rw [Scheme.basicOpen_mul]
    refine ⟨hzf, ?_⟩
    show z ∈ X.basicOpen _
    rw [Scheme.mem_basicOpen _ _ _ hz]
    exact IsLocalization.map_units L
      (⟨_, Submonoid.prod_mem _ fun τ _ => hg τ⟩ : (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)
  · rw [Scheme.basicOpen_mul]
    exact inf_le_left.trans hfU
  · have q := hB₀ τ _ ρ (isUnit_of_dvd_unit
      (map_dvd ρ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)).mul_left f)) hu)
    exact exists_eigBasisAt hx' _ (fun i => ρ ∘ B₀ τ i) (fun i => by rw [← q.1 i]; exact (hP' τ _).1)
      fun v hv => q.2 v ((hP' τ v).2 hv)

variable {D : Datum H}

theorem lieMult_univ (Xo : Moduli D l) (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ Xo.XF c)
    (hy : y ≫ pullback.snd _ _ = spMap φ) (τ : E →+* ℂ) :
    LieMult Xo.univ.t.act (y ≫ pullback.fst _ _) (φ.comp (embK c τ)) (D.mult τ) := by
  have hd := (Xo.univ.geom k (y ≫ pullback.fst _ _) (φ.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm)).1 (φ.comp (embK c τ))
  unfold Datum.mult
  split_ifs with h
  · exact hd.1 (congrArg φ (Subtype.ext h))
  · exact hd.2 fun h' => h (congrArg Subtype.val (φ.injective h'))

theorem mult_conj {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) : D.mult (conjEmb τ) = D.q := by
  refine if_neg fun h => ?_
  have h3 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h
  rw [hτ] at h3
  have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3
  have h6 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  simp [pow_two, h5] at h6
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.DetLine.CoverU

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.DetLine
  GlobalTheory.DetLine.CoverU in

theorem GlobalTheory.DetLine.frameCover_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) D.p D.q := by
  intro E _ _ _ H D l Xo c U τ hτ z hz
  obtain ⟨W, hW, j, hzW, hWU, hj, hb⟩ :=
    exists_affine_bases (t := Xo.univ.t) c (toX Xo c) (toF Xo c) D.mult (lieMult_univ c Xo) U z hz
  have h₁ := hb τ
  have h₂ := hb (conjEmb τ)
  rw [show D.mult τ = D.p from if_pos hτ] at h₁
  rw [mult_conj hτ] at h₂
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  refine ⟨W, hW, j, v, w, hzW, hj, hW.range_fromSpec.le.trans hWU, hv, ?_⟩
  rw [comp_chi_bar]
  exact hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPerpKerEquivHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.PerpKerRank

theorem exists_eStd_eq_addHom (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  obtain ⟨a, ha⟩ := (eStdBilin_bijective (g := g) (n := n)).2 (φ.toZModLinearMap n)
  exact ⟨a, fun b => LinearMap.congr_fun ha b⟩

theorem nonempty_perp_ker_equiv_hom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy) :
    Nonempty (S.perp yy.ker ≃+ (X →+ ZMod (S.r * S.N))) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  refine ⟨AddEquiv.ofBijective Λ ⟨(injective_iff_map_eq_zero _).2 fun t ht =>
    Subtype.ext (eq_zero_of_eStd_eq_zero fun b => ?_), fun l => ?_⟩⟩
  · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
    rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
  · let l' : (X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ l (by
        rintro _ ⟨x, rfl⟩
        show l ((S.r * S.N) • x) = 0
        rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq_addHom S.g _ (l'.comp yy)
    refine ⟨⟨a, fun h hh => (ha h).trans ?_⟩, AddMonoidHom.ext fun α => (ha (σ α)).trans ?_⟩
    · rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hh, map_zero]
    · rw [AddMonoidHom.comp_apply, hσ]
      rfl

theorem perp_ker_equiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range), Function.Surjective yy → S.IsoFree (S.perp yy.ker) → Nonempty (S.perp yy.ker ≃+ (Fin (Module.finrank ℤ X) → ZMod (S.r * S.N))) := by
  intro o Ω _ _ _ S X _ _ _ yy hs _
  obtain ⟨e⟩ := nonempty_perp_ker_equiv_hom S yy hs
  exact ⟨e.trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩

end GlobalTheory.ZH.PerpKerRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUniformizerConstantStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_uniformizer_constant : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ ϖ : V, Irreducible ϖ → ∃ r : ℝ, ∀ φ : V →+* 𝓞_ℂ_[p], ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = r := by
  first | exact @GlobalTheory.unif_norm_indep | exact GlobalTheory.unif_norm_indep | (intros; apply GlobalTheory.unif_norm_indep <;> assumption)
end
end

