import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidue
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
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClosureDim

theorem ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero (F : Type) [Field F]
    {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra.FiniteType F A]
    (φ : A →+* B)
    (hB : @Algebra.FiniteType F B _ _ (φ.comp (algebraMap F A)).toAlgebra)
    (Q : Ideal B) [Q.IsPrime]
    (h : @Algebra.trdeg (Q.comap φ).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap φ) Q φ rfl).toAlgebra = 0) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap φ) := by
  letI : Algebra F B := (φ.comp (algebraMap F A)).toAlgebra
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set P := Q.comap φ
  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.map P Q φ rfl).toAlgebra
  haveI : IsScalarTower F P.ResidueField Q.ResidueField := IsScalarTower.of_algebraMap_eq fun f ↦ by
    change algebraMap F Q.ResidueField f = Ideal.ResidueField.map P Q φ rfl (algebraMap F P.ResidueField f)
    rw [IsScalarTower.algebraMap_apply F A P.ResidueField, Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply F B Q.ResidueField]
    rfl
  haveI : Algebra.FiniteType F (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType F (B ⧸ Q) :=
    haveI := hB; Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) Ideal.Quotient.mk_surjective
  have hfaith (S : Type) [CommRing S] [Nontrivial S] [Algebra F S] : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).mpr (algebraMap F S).injective
  haveI := hfaith (A ⧸ P); haveI := hfaith (B ⧸ Q); haveI := hfaith P.ResidueField
  haveI : FaithfulSMul (A ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Q.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul P.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  haveI : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ P))
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (B ⧸ Q))
  have h₁ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (A ⧸ P) P.ResidueField
  have h₂ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (B ⧸ Q) Q.ResidueField
  have h₃ := trdeg_add_eq F P.ResidueField (A := Q.ResidueField)
  rw [h, add_zero] at h₃
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq F (A ⧸ P)
  rw [hd₁]
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq F (B ⧸ Q) (by rw [← h₂, ← h₃, h₁, hd₂])

end GlobalTheory.ClosureDim

namespace GlobalTheory.ClosureDim

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X)
    (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y),
    (letI := (π.residueFieldMap y).hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) →
    topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  intro F _ Y X π sX _ _ y halg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (π ⁻¹ᵁ U : Set Y) from hxU)
      (π ⁻¹ᵁ U).isOpen
  have hV : IsAffineOpen V := hV
  have e : V ≤ π ⁻¹ᵁ U := hVU
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  let φ := π.appLE U V e
  have hsq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hU hV e
  have hpt : π (hV.fromSpec p) = hU.fromSpec (Spec.map φ p) := by
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have h0 : @Algebra.trdeg (X.residueField (π (hV.fromSpec p))) (Y.residueField (hV.fromSpec p)) _ _
      (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra = 0 := by
    letI := (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra
    exact trdeg_eq_zero (R := X.residueField (π (hV.fromSpec p))) (A := Y.residueField (hV.fromSpec p))
  rw [GlobalTheory.RelDimFibCrit.trdeg_affine π U hU V hV e p] at h0
  let ψ := Spec.preimage (hU.fromSpec ≫ sX)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sX := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  have hA : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hB : @Algebra.FiniteType F Γ(Y, V) _ _ (φ.hom.comp (algebraMap F Γ(X, U))).toAlgebra := by
    have h : Spec.map (ψ ≫ φ) = hV.fromSpec ≫ π ≫ sX := by
      rw [Spec.map_comp, hψ, ← Category.assoc, hsq, Category.assoc]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ ≫ φ)).mp (h ▸ inferInstance)
  rw [hpt, GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient (π ≫ sX) hV.fromSpec p,
    GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient sX hU.fromSpec (Spec.map φ p)]
  haveI := p.isPrime
  exact ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero F φ.hom hB p.asIdeal h0

end GlobalTheory.ClosureDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem qLevel_of_torsion_labels : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hI
  intro g k hk ζ pt hζ hadd hinj hsurj hw
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.ZH.uTors_closed V hV A G D U C k hk
  obtain ⟨-, -, hAdd, -, hQ⟩ := GlobalTheory.Ex.GtValues.points_correspond V D.toPre D.psi_even D.tau_bimult C N ν
  have hWp := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2) V D.toPre D.psi_even D.tau_bimult C N ν k hk
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ k

  have hmul : ∀ (p₁ p₂ p₃ : QkPt D.toPre C k) (q₁ q₂ : N.QT k), ν.QPt p₁ q₁ → ν.QPt p₂ q₂ → ν.QPt p₃ (q₁ * q₂) →
      f p₃ = f p₁ * f p₂ := by
    intro p₁ p₂ p₃ q₁ q₂ h₁ h₂ h₃
    apply hf4
    refine ⟨p₃, ?_, ?_, ?_⟩
    · rw [← h₃.1, ← h₁.1, ← h₂.1]
      exact map_add ν.eX _ _
    · exact (hAdd _ _ _ _ _ _ h₁.2 h₂.2 h₃.2).2 rfl
    · exact (hQ3 p₃ p₃ _ _ h₃ h₃).2 ((N.qEq_equivalence k).refl _)

  have hpt0 : pt 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hptn : ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
    intro n a
    induction n with
    | zero => simpa using hpt0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hkt : ∀ a, pt a ^ k = 1 := by
    intro a
    have : k • a = 0 := by
      funext i
      simp [nsmul_eq_mul, ZMod.natCast_self]
    rw [← hptn, this, hpt0]
  have hex : ∀ a, ∃ p, f p = pt a := fun a => hf2 (pt a) (hkt a)
  choose p hp using hex
  have hexq : ∀ a, ∃ q, ν.QPt (p a) q := fun a => (hQ1 (p a)).exists
  choose q hq using hexq

  have hpow : ∀ (q' : N.QT k) (p' : QkPt D.toPre C k), ν.QPt p' q' → ∀ (n : ℕ) (pn : QkPt D.toPre C k),
      ν.QPt pn (q' ^ n) → f pn = f p' ^ n := by
    intro q' p' hp' n
    induction n with
    | zero =>
      intro pn hpn
      rw [pow_zero] at hpn ⊢
      have h := hmul pn pn pn 1 1 hpn hpn (by rw [_root_.mul_one]; exact hpn)
      exact (mul_eq_left.1 h.symm)
    | succ n ih =>
      intro pn hpn
      obtain ⟨pm, hpm⟩ := hQ2 (q' ^ n)
      rw [pow_succ] at hpn
      rw [hmul pm p' pn _ _ hpm hp' hpn, ih pm hpm, pow_succ]
  have hqk : ∀ q' : N.QT k, q' ^ k = N.qTriv k (Multiplicative.toAdd q'.1.1) := by
    intro q'
    apply Subtype.ext
    apply Prod.ext
    · show q'.1.1 ^ k = Multiplicative.ofAdd (k • Multiplicative.toAdd q'.1.1)
      rw [ofAdd_nsmul, ofAdd_toAdd]
    · show q'.1.2 ^ k = N.io (Multiplicative.toAdd q'.1.1)
      exact (N.mem_QT).1 q'.2
  refine ⟨p, q, ⟨hζ, ?_, ?_, ?_, ?_⟩, fun a => ⟨hq a, (hf1 _ _).2 (hp a).symm⟩⟩
  · intro a b
    obtain ⟨p'', hp''⟩ := hQ2 (q a * q b)
    have h : f p'' = f (p (a + b)) := by rw [hmul _ _ _ _ _ (hq a) (hq b) hp'', hp, hp, hp, hadd]
    exact (hQ3 _ _ _ _ hp'' (hq (a + b))).1 ((hf3 _ _).1 h)
  · intro a b h
    apply hinj
    rw [← hp, ← hp]
    exact (hf3 _ _).2 ((hQ3 _ _ _ _ (hq a) (hq b)).2 h)
  · intro q'
    obtain ⟨p', hp'⟩ := hQ2 q'
    obtain ⟨p₀, hp₀⟩ := hQ2 1
    obtain ⟨pk, hpk⟩ := hQ2 (q' ^ k)
    have h0 := hpow q' p' hp' 0 p₀ (by rw [pow_zero]; exact hp₀)
    have hk' := hpow q' p' hp' k pk hpk
    have heq : N.QEq 1 (q' ^ k) := (N.qEq_iff _ _).2 ⟨_, by rw [_root_.one_mul]; exact hqk q'⟩
    have h1 : f p₀ = f pk := (hf3 _ _).2 ((hQ3 _ _ _ _ hp₀ hpk).2 heq)
    have htor : f p' ^ k = 1 := by rw [← hk', ← h1, h0, pow_zero]
    obtain ⟨a, ha⟩ := hsurj (f p') htor
    refine ⟨a, (hQ3 _ _ _ _ (hq a) hp').1 ((hf3 _ _).1 ?_)⟩
    rw [hp, ha]
  · intro i j
    have h := hw i j
    rw [← hp, ← hp] at h
    have h' := (hf5 _ _ (ζ ^ stdSymp g i j)).2 h
    exact Units.ext ((hWp _ _ _ _ _ (hq _) (hq _)).1 h').symm

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.JcSmul

theorem valR_const_mul {F A : Type} [Field F] [CommRing A] [Algebra F A] {Y : Scheme.{0}} (r : Sp A ⟶ Y)
    (π : Y ⟶ Sp F) (h : r ≫ π = spMap (algebraMap F A)) (U : Y.Opens) (z : F) (f : Γ(Y, U)) :
    valR r U (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) * f) =
      algebraMap F A z * valR r U f := by
  unfold valR
  by_cases hU : ⊤ ≤ r ⁻¹ᵁ U
  · rw [dif_pos hU, dif_pos hU, map_mul, map_mul]
    congr 1
    have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z))) =
        (r ≫ π).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
      simp only [resTop]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply]
      exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp A, ⊤) => g.hom (π.appTop.hom _)) (Scheme.Hom.appLE_eq_app r (U := ⊤))
    rw [e, h]
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F A))
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  · rw [dif_neg hU, dif_neg hU, mul_zero]

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  intro R _ _ D F _ _ N ν k s a gm α
  have e : (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ≫
      (fst (TF (R := R) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  unfold jc sE
  rw [← _root_.mul_assoc]
  congr 1
  have h2 : (TrivSqZeroExt.inl a : DualNumber F) = algebraMap F (DualNumber F) a := rfl
  rw [h2]
  exact valR_const_mul _ _ e _ a _

end GlobalTheory.JcSmul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionCharacterValueConstantTermOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl

theorem fst_vE_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  intro R _ _ D _ N ν gm ⟨o, hz, hp⟩ χ
  have hJ : Good D.P.L (IsLocalRing.closedPoint ℂ) ν.J := fun ψ => ν.good ψ trivial
  have hm : redE ℂ (IsLocalRing.closedPoint ℂ) ∈ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    simpa only [Category.id_comp] using hJ.mem (DegPre.gtφT D (TE R ℂ) gm.b χ) (redE ℂ)
  have h : ⊤ ≤ (𝟙 (Sp (DualNumber ℂ))) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    refine (GlobalTheory.KS.TangentAt.top_le_iff_dual _ _).2 ((GlobalTheory.ZH.CrdCalc.top_le_iff _ _).2 ?_)
    rw [Category.comp_id]
    exact hm
  have e1 : valR (redE ℂ ≫ 𝟙 (Sp (DualNumber ℂ))) (LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)))
      ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val = (vE (gm.s χ) (𝟙 _) ν.J).fst :=
    (GlobalTheory.ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _) _ h).2 _
  rw [Category.comp_id] at e1
  have e2 := GlobalTheory.ZH.ThetaData.valR_eq_gs (redE ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val
  have e3 := gs_unit (redE ℂ) (IsLocalRing.closedPoint ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k))
  have e4 := val_of (gm.s χ) (redE ℂ) (IsLocalRing.closedPoint ℂ) ν.J
    (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) (fun k => by rw [Category.id_comp])
  have v1 := val_pull hJ (gm.s χ) (redE ℂ) (𝟙 _)
  rw [Category.id_comp] at v1
  have v2 := (val_corr hJ (hp.2 χ) (𝟙 _)).symm.trans ((val_corr hJ (hz.2 χ) (𝟙 _)).trans (val_one _))
  rw [v1] at v2
  refine e1.symm.trans (e2.trans ?_)
  rw [e3, ← e4, v2, Units.val_one, map_one]

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDualCharValuesMulCube
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.DualMult

theorem redE_closedPoint :
    (redE ℂ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (DualNumber ℂ) := by
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  exact Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)

variable {X : Scheme.{0}} {L : LB X}

theorem good_dual (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    Good L (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ)) := by
  intro ψ
  have h := hJ (redE ℂ ≫ ψ) (x := IsLocalRing.closedPoint ℂ) trivial
  change ψ ((redE ℂ) (IsLocalRing.closedPoint ℂ)) ∈ L.U (J (redE ℂ ≫ ψ)) at h
  rwa [redE_closedPoint] at h

theorem vE_eq_val (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {K : Type} [Fintype K]
    {φ : K → (Sp (DualNumber ℂ) ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) :
    vE t (𝟙 _) J = (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (val t (𝟙 _) (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ))).val := by
  have hm := (good_dual J hJ).mem φ (𝟙 _)
  unfold vE val
  exact (GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ hm _).trans (congrArg _ (gs_unit _ _ _ hm _))

end GlobalTheory.DualMult

namespace GlobalTheory.DualMult
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem mult_vE (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X) :
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  have hJ := good_dual (L := D.P.L) ν.J ν.good
  have e := val_corr hJ (gm.mult χ χ') (𝟙 _)
  replace e := (val_mul hJ _ _ _).symm.trans (e.trans (val_mul hJ _ _ _))
  refine (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).trans
    (Eq.trans ?_ (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).symm)
  rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul]
  exact congrArg (fun u => (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom (Units.val u)) e

end GlobalTheory.DualMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr

theorem gBig_two {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

theorem dictionary_at_stage : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
      GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
        HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_two GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    GlobalTheory.T.seesawTriple_firstFiniteDatum_riggedFrames X _ _ _ _ _ _ _ _ e1 e2 hXi t, GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
  · refine
      { hecA := (hXi.weil' t).hecS
        hecB := (hXi.weil t).hecS
        resA := (hXi.weil' t).resS
        resB := (hXi.weil t).resS
        rank := hrk
        even := by rw [hrk]; exact hsz.1
        sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
        ram := hram W i j p q A A' WW X ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ t }
    have h1 := (hab t τ).2.2
    have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast (hrk ▸ hsz.2.2.2)
    linarith
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ := funext e1
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B := funext (onb_rigFr X.rA hXi.rigA)
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [f1, f2, f3, f4]
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s := funext e1'
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B := funext (onb_rigFr X.rA' hXi.rigA')
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [f1, f2, f3, f4]
    rfl

end GlobalTheory.StageDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAtStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_tuple_at : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → TwAdm → TwChr → GlobalTheory.BigOn.Exp.TwConj.TupAt := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.tupAt | exact GlobalTheory.BigOn.Exp.TwConj.tupAt | (intros; apply GlobalTheory.BigOn.Exp.TwConj.tupAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSumsStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums : DeepGood → Size → Deg → Share → Height → HS → SumC → ULow := by
  first | exact @GlobalTheory.CovTop.FromComp.uLow_of | exact GlobalTheory.CovTop.FromComp.uLow_of | (intros; apply GlobalTheory.CovTop.FromComp.uLow_of <;> assumption)
end

