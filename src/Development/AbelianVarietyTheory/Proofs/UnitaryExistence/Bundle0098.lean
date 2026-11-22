import Mathlib
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesStOfLandherrOfHasseNorm
section
theorem GlobalTheory.allClassesSt_of_landherr_of_hasseNorm :
    GlobalTheory.Published.LandherrSt → GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hL hN => GlobalTheory.all_classes_occur hL hN GlobalTheory.abelianSchemeLaws_all.1 (GlobalTheory.T.exists_heckeQuotient_principal_triple GlobalTheory.abelianSchemeLaws_all.1)

theorem GlobalTheory.allClassesSt_of_hasseNorm : GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hN => GlobalTheory.allClassesSt_of_landherr_of_hasseNorm
    (GlobalTheory.Published.landherrSt_of_landherr (GlobalTheory.LocalQuad.landherr_of_hasseNormSt hN)) hN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsFiniteDimensionalOfGoodEmb
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem cuspForms_finiteDimensional_of_goodEmb :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ) → Formalism.L2.Pj.CuspFD Xo c U := by
  intro E _ _ _ H Dw l Xo c r U σ hσ hU
  exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ)
      ((Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 hU))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecBCIffSecBCTest
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.SecFieldCompare

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map
  map_cancel hasBC_of exists_testRing_ext)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests (IsBCTest SecBCTest SecBCAll)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def homRes {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T) : S →ₐ[c.F] T :=
  { ψ.toRingHom with
    commutes' := fun a => by
      show ψ (algebraMap c.F S a) = algebraMap c.F T a
      rw [← hS a, ψ.commutes, hT a] }

theorem frMap_res_iff {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (homRes hle hS hT ψ) (y.res hle hS) (z.res hle hT) ↔ FrMap ψ y z := Iff.rfl

theorem fromT_of_res (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (hy : FromT (y.res hle h)) : FromT y := by
  obtain ⟨p, φ, y₀, hy₀⟩ := hy
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  obtain ⟨q, α, hα, hlift, -⟩ := exists_testRing_ext (K' := c'.F) p
  obtain ⟨β, hβ⟩ := hlift S φ.toRingHom fun a => (φ.commutes a).trans (h a).symm
  let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
  have hq : AlgOver c c' hle q.R := fun _ => rfl
  let α' : p.R →ₐ[c.F] q.R := { α with commutes' := hα }
  obtain ⟨y₁, hy₁⟩ := hBC _ _ α' y₀
  have e : (homRes hle hq h β).comp α' = φ := AlgHom.ext hβ
  have h₂ : FrMap (homRes hle hq h β) y₁ (y.res hle h) := map_cancel hBC e hy₁ hy₀
  exact ⟨q, β, y₁.ext hle hq, (frMap_res_iff hle hq h β (y₁.ext hle hq) y).1 h₂⟩

theorem isBCTest_of_isBC (hWD : ValueWD Xo c) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F} {fs : Fin m → Rul Xo c}
    (hf' : Natural c' f') (hfs : ∀ i, Natural c (fs i)) (h : IsBC hle f' as fs) : IsBCTest hle f' as fs := by
  intro p' _ hp y' p φ y hy
  rw [← evR_test hf' p' y', h p'.R hp y']
  exact Finset.sum_congr rfl fun i _ => congrArg _ (evR_of_map hWD (hfs i) hy)

theorem isBC_of_isBCTest (hWD : ValueWD Xo c) (hBC : HasBC Xo c) (hT : AllTest Xo c) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hfs : ∀ i, Natural c (fs i)) (h : IsBCTest hle f' as fs) :
    IsBC hle f' as fs := by
  intro S _ _ _ hS y
  by_cases hy : FromT y
  · obtain ⟨q, ψ, y', hy', hev⟩ := evR_spec hy
    let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
    have hq : AlgOver c c' hle q.R := fun _ => rfl
    have : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced _).1 q.rad
    obtain ⟨p, φ, y₀, hy₀⟩ := hT q.R (y'.res hle hq)
    have h₂ := map_trans _ _ hy₀ ((frMap_res_iff hle hq hS ψ y' y).2 hy')
    rw [hev, h q hq y' p φ y₀ hy₀, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ψ.commutes, evR_of_map hWD (hfs i) h₂]
    rfl
  · have hy' : ¬ FromT (y.res hle hS) := fun h' => hy (fromT_of_res hle hBC hS y h')
    rw [evR_not hy]
    exact (Finset.sum_eq_zero fun i _ => by rw [evR_not hy', mul_zero]).symm

theorem isBC_iff_isBCTest {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F} {fs : Fin m → Rul Xo c}
    (hf' : Natural c' f') (hfs : ∀ i, Natural c (fs i)) : IsBC hle f' as fs ↔ IsBCTest hle f' as fs :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  ⟨isBCTest_of_isBC hle hWD hf' hfs,
    isBC_of_isBCTest hle hWD (hasBC_of hS) (GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c) hfs⟩

variable (Xo)

theorem secBC_iff_secBCTest (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n ↔ SecBCTest Xo hle a n :=
  forall₂_congr fun _ hf' => exists₃_congr fun _ _ _ => and_congr_right fun hfs =>
    isBC_iff_isBCTest hle hf'.1 fun i => (hfs i).1

theorem secBC_iff_forall : Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n := Iff.rfl

theorem secBC_typings_equiv :
    (Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n) ∧
    (Formalism.L2.Pj.SecBC Xo hle ↔ SecBCAll Xo hle) ∧
    (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
      f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) → (IsBC hle f' as fs ↔ IsBCTest hle f' as fs)) ∧
    (Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, SecBCTest Xo hle a n) :=
  ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ _ _ hf' hfs => isBC_iff_isBCTest hle hf'.1 fun i => (hfs i).1,
    forall₂_congr fun a n => secBC_iff_secBCTest Xo hle a n⟩

end GlobalTheory.SecFieldCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VVRank (pullS isPullSec_pullS)
open GlobalTheory.TwistBaseChange (eq_pullS_of_isPullSec)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaRuleCompare

section Descent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem sec_ext {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

omit [GrpObj A] in
theorem chart_ge {T T' : Over S} (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  have h1 : ((h ▷ A).left ≫ (snd T A).left).base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  rw [← Over.comp_left, whiskerRight_snd] at h1
  exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1

theorem gs_pullS {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((pullS A a h s).f j) = gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullS A a h' (pullS A a h s) = pullS A a (h' ≫ h) s :=
  sec_ext fun j => fn_ext fun y hy => by
    refine (gs_pullS h' _ _ y j hy).trans ((gs_pullS h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

theorem exists_descend {T T' : Over S} (π : T' ⟶ T) [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (F' : LB.Sec (LPow A L a T'))
    (H : ∀ (T'' : Over S) (g₁ g₂ : T'' ⟶ T'), g₁ ≫ π = g₂ ≫ π → pullS A a g₁ F' = pullS A a g₂ F') :
    ∃ F : LB.Sec (LPow A L a T), pullS A a π F = F' := by
  have P := (isPullback_whisker (A := A) π).flip
  have : Flat (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have : Surjective (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have : QuasiCompact (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have appLE : ∀ {Z Y : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (b : Γ(Y, U)) (z : Z),
      gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom b) = gs g z U b := fun {Z Y} g U h b z =>
    (gs_res (𝟙 Z) z h trivial ((g.app U).hom b)).trans
      ((gs_pull (𝟙 Z) g z U (h (x := z) trivial) b).trans (by rw [Category.id_comp]))
  have desc : ∀ j : Fin 1 → L.ι, ∃ b : Γ((T ⊗ A).left, (LPow A L a T).U j), ((π ▷ A).left.app _).hom b =
      ((T' ⊗ A).left.presheaf.map (homOfLE (chart_ge π j)).op).hom (F'.f j) := fun j => by
    refine FunDescent.exists_app_eq _ _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [appLE, appLE, gs_res _ z _ (h₁ (x := z) trivial), gs_res _ z _ (h₂ (x := z) trivial)]
    have w : g₂ ≫ (T' ⊗ A).hom = g₁ ≫ (T' ⊗ A).hom := by
      rw [← Over.w (π ▷ A), ← Category.assoc, ← e, Category.assoc]
    let G₁ : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A := Over.homMk g₁ rfl
    let G₂ : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A := Over.homMk g₂ w
    have E : G₁ ≫ π ▷ A = G₂ ≫ π ▷ A := Over.OverMorphism.ext e
    have E₁ : (G₁ ≫ fst _ _) ≫ π = (G₂ ≫ fst _ _) ≫ π := by
      rw [Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, E, Category.assoc]
    have E₂ : G₂ ≫ snd _ _ = G₁ ≫ snd _ _ := by
      rw [← whiskerRight_snd π, ← Category.assoc, ← E, Category.assoc]
    have k : ∀ G : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A, G ≫ snd _ _ = G₁ ≫ snd _ _ →
        G.left z ∈ (LPow A L a T').U j → gs G.left z _ (F'.f j) =
          gs (lift (𝟙 _) (G₁ ≫ snd _ _)).left z _ ((pullS A a (G ≫ fst _ _) F').f j) := fun G hG hz => by
      have e' : (lift (𝟙 _) (G₁ ≫ snd _ _)).left ≫ ((G ≫ fst _ _) ▷ A).left = G.left := by
        rw [← Over.comp_left, lift_whiskerRight, Category.id_comp, ← hG, ← comp_lift, lift_fst_snd,
          Category.comp_id]
      refine Eq.trans ?_ (gs_pullS _ _ _ z j (chart_ge (G ≫ fst _ _) j ?_)).symm
      · rw [e']
      · exact (congrArg (fun q => q z ∈ (LPow A L a T').U j) e').mpr hz
    exact (k G₁ rfl (chart_ge π j (h₁ (x := z) trivial))).trans
      ((congrArg (fun u => gs _ z _ (LB.Sec.f u j)) (H _ _ _ E₁)).trans
        (k G₂ E₂ (chart_ge π j (h₂ (x := z) trivial))).symm)
  choose b hb using desc
  have hv : ∀ j (w : (T' ⊗ A).left), (π ▷ A).left w ∈ (LPow A L a T).U j →
      gs (𝟙 _ ≫ (π ▷ A).left) w _ (b j) = gs (𝟙 _) w _ (F'.f j) := fun j w hw =>
    (gs_pull (𝟙 _) _ w _ hw _).symm.trans ((congrArg (gs (𝟙 _) w _) (hb j)).trans
      (gs_res (𝟙 _) w (chart_ge π j) hw _))
  refine ⟨⟨b, fun j j' => FunDescent.app_injective (π ▷ A).left _ (fn_ext fun w hw => ?_)⟩,
    sec_ext fun j => fn_ext fun w hw => ?_⟩
  · have hw' : (𝟙 _ ≫ (π ▷ A).left) w ∈ (LPow A L a T).U j ⊓ (LPow A L a T).U j' := hw
    refine (gs_pull (𝟙 _) _ w _ hw' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ w _ hw' _).symm)
    refine ((gs_res _ w _ hw' _).trans ((hv j w hw'.1).trans
      (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T' A).left) (ε := fun _ => a) F' (𝟙 _) w
        (chart_ge (a := a) π j hw'.1) (chart_ge (a := a) π j' hw'.2)))).trans (Eq.symm ?_)
    refine (gs_mul _ w _ hw' _ _).trans (congrArg₂ (· * ·) ((gs_unit _ w _ hw' _).trans (congrArg Units.val
      ((gm_linComb L _ _ _ w j j' hw'.1 hw'.2).trans ?_))) ((gs_res _ w _ hw' _).trans (hv j' w hw'.2)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, VVRank.whisker_snd_left]
  · exact (gs_pullS π _ _ w j hw).trans (hv j w (chart_le_res A L (π ▷ A) (whiskerRight_snd _ _) a j hw))

end Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

section Auxiliary

variable (Xo : Moduli Dw l) (c : Coeff l)

def jetEquiv : NabV Xo c ≃ IndefiniteRowSideFullHecke.ColumnSectionIdeal.Jet Xo c where
  toFun nab := fun _ _ _ y k F m => nab y k F (Finsupp.equivFunOnFinite.symm m)
  invFun J := fun {S} _ _ y k F α => J S y k F α
  left_inv nab := by
    funext S _ _ y k F α
    exact congrArg (nab y k F) (Finsupp.equivFunOnFinite_symm_coe α)
  right_inv J := rfl

variable {Xo c}

end Auxiliary

section Translates

variable (Xo : Moduli Dw l)

def LocVt {T : Over Xo.X} (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (t : T ⟶ Xo.univ.t.G)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) T)) : Prop :=
  ∀ p : T.left, ∃ (T' : Over Xo.X) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) (pullS _ _ π s) (π ≫ t) (pullS _ _ π F)

variable {Xo}

end Translates

section Values

variable {Xo : Moduli Dw l} {c : Coeff l}

def ExprNatural (nab : NabV Xo c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S')
    (y : FrPt Xo c S) (y' : FrPt Xo c S'), ψ.toRingHom.FaithfullyFlat → FrMap ψ y y' →
    ∀ h : ptO Xo y'.x ⟶ ptO Xo y.x, h.left = spMap ψ.toRingHom →
    ∀ F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)),
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab y' P fun b => pullS _ _ h (F b)

def domainJump (Xo : Moduli Dw l) (c : Coeff l) : NabV Xo c :=
  fun {S} _ _ _ _ _ _ => open Classical in if IsDomain S then 0 else 1

end Values

end GlobalTheory.ThetaRuleCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFrameDetMulSqInvariantUncond
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 :=
  thetaFrame_det_mul_sq_invariant latMinkowski abelianSchemeLaws_all.2.secTwist
    theta_sq_transform_level_eight

end GlobalTheory
end
end

