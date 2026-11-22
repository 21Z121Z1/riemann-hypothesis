import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Formalism.SatakeDualWeyl.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodTypeNoChi

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem p_comp : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c c' : G → ℂ) (F : GA D V → ℂ),
    HasType V β (flag1L L) F →
      gaL V β L eG c (gaL V β L eG c' F) = gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F := by
  intro D V β L hL G _ _ eG c c' F hF
  have hm : ∀ y z : G, actL V β L (eG y) (actL V β L (eG z) F) = actL V β L (eG (y * z)) F := fun y z => by
    rw [map_mul]
    exact Formalism.IndefR.Eqv.Act.levelGroupAction_mul_of_lifts hL (eG y) (eG z) hF
  have lhs : gaL V β L eG c (gaL V β L eG c' F) =
      ∑ y : G, ∑ z : G, (c y * c' z) • actL V β L (eG (y * z)) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [mul_comm]
  have rhs : gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F =
      ∑ y : G, ∑ x : G, (c y * c' (y⁻¹ * x)) • actL V β L (eG x) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun z => by simp

theorem p_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ (i : Fin D.R.m) (t : T), LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i t
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem isClass_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem charLab_inv {g : ℕ} [Fact g.Prime] {L : LabelDatum g} {θ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (h : GlobalTheory.GLp.IsCharLab L θ c) : GlobalTheory.GLp.IsCharLab L θ⁻¹ c⁻¹ := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨inv_ne_zero hc, fun u hu => ?_⟩
  have e1 : ((θ⁻¹ u : ℂˣ) : ℂ) = ((θ u : ℂˣ) : ℂ)⁻¹ := by simp
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective]
  have e2 : L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c⁻¹) = (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))⁻¹ := by
    rw [map_inv₀]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  rw [e1, hv u hu, e2]

theorem seriesKillsAvg : SeriesKillsAvg := by
  intro g _ L r f θ c hc hf hf' a b ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    cases r with
    | zero => exact absurd (_root_.funext fun i : Fin 0 => Fin.elim0 i) ha
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hfin, -⟩ := irr_finite_and_finsum_zOf_eq_one (Gn g (n + 1))
  rw [eSerC_eq_sum L (n + 1) hfin f, Finset.sum_mul]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hψ
  obtain ⟨hirr, hlab⟩ := hψ
  apply GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero g (n + 1) ψ hirr θ a b
  rw [GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep g n ψ (isClass_irr hirr) θ a ha b]
  have hinv := charLab_inv hc
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).1]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).1 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).1 hip)
  · simp only [if_true]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).2]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).2 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).2 hip)

theorem goodNoChi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hc : GlobalTheory.Hk3.Core R F := hG.core
  have hl : R.toLevCh.Is A.μ0 := hc.lev
  have hL : LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := p_lifts D G Pl0 T A Ks R hl i t
  intro y hy PP a ha b ε hε l
  have hT : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) :=
    GlobalTheory.T.definiteSpace_forms_functional_principalType D G Pl0 T A Ks R F hc i t y l
  have hy' := hy l
  have e1 := p_comp _ _ _ hL R.eG (mirC R i PP a b ε) (RealDat.eC (A := A) (sg0 D A)) _ hT
  have e0 := congrArg (gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a b ε)) hy'
  have h0 : (fun x => ∑ y, mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x)) = fun _ => 0 :=
    funext (GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero seriesKillsAvg D G Pl0 T A Ks R F hG i PP a ha b ε hε)
  have e2 := congrArg (fun c => gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG c (fun h => l (R.extV i t y h))) h0
  have e3 : gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (fun _ : G => (0 : ℂ)) (fun h => l (R.extV i t y h)) = 0 := by
    simp only [gaL, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  exact e0.symm.trans (e1.trans (e2.trans e3))

end GlobalTheory.GoodTypeNoChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
section
noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨ ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) → RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  first | exact @GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | exact GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | (intros; apply GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfRowsGuarded
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSpan

theorem hkSS_of_rows_guarded {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y)
    (hG : CommG D) (hC : HkComm D) (hSF : SupFull D)
    (X : NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0))
    (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (hEmb : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x,
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x))
    (hBr : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i))
    (hSp : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits) :
    HkSS D := by
  intro i hi j hj b
  have := D.nexp.towFm i j b

  have hspan : ∀ x ∈ V0 D.nexp i j b,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (Set.range (D.nexp.embB i j b)) := by
    intro x hx
    have hx' : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) := by
      rw [(hSF i hi j hj b).2]; exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 hx'
    rw [Submodule.span_eq] at hy
    have hyV : y ∈ V0 D.nexp i j b := by
      have e : y = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (z : D.ntw.O i)) •
          (IsLocalization.mk' (FractionRing (D.ntw.O i)) (1 : D.ntw.O i) z • y) := by
        rw [smul_smul, mul_comm, IsLocalization.mk'_spec, map_one, one_smul]
      rw [e]; exact Submodule.smul_mem _ _ hx
    have hyR : y ∈ LinearMap.range (D.nexp.embB i j b) := by
      rw [hBr i hi j hj b]
      exact Submodule.mem_inf.2 ⟨hy, (Submodule.restrictScalars_mem _ _ _).2 hyV⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.1 hyR))

  have hpoly : ∀ k P, HkIdx i k P → ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧ p.Splits ∧
      ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
    intro k P hkP
    obtain ⟨p1, hp10, hp1s, hp1k⟩ := GlobalTheory.T.split_charpoly_lattice_kills_span (D.ntw.O i) (D.nexp.Fm i j b) (D.ntw.B i j b)
      (D.nexp.embB i j b) (D.ntw.hk i j b k P) (D.nexp.hkF i j b k P) (hEmb i hi j hj b k P hkP)
      (hSp i hi j hj b k P hkP)
    obtain ⟨p2, hp2s, hp2k⟩ :=
      GlobalTheory.GoodSS.hkF_separable Rl F cG S Y H hG hC X hR hU hI hS0c hS02 hS0b i hi j hj b k P hkP
    classical
    refine ⟨EuclideanDomain.gcd p1 p2, hp2s.of_dvd (EuclideanDomain.gcd_dvd_right _ _),
      hp1s.of_dvd hp10 (EuclideanDomain.gcd_dvd_left _ _), ?_⟩
    intro x hx
    rw [EuclideanDomain.gcd_eq_gcd_ab, mul_comm p1, mul_comm p2, map_add, map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp1k x (hspan x hx), hp2k x hx,
      map_zero, map_zero, add_zero]

  have hJ := GlobalTheory.JointDiag.le_iSup_jointEigenspace_inf (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) {a : ℕ × PlE D.host // HkIdx i a.1 a.2}
    (fun a => D.nexp.hkF i j b a.1.1 a.1.2) (V0 D.nexp i j b)
    (fun a c => hC i hi j hj b _ _ _ _ a.2 c.2)
    (fun a x hx => GlobalTheory.T.hecke_preserves_good_part D hG i hi j hj b _ _ a.2 x hx)
    (fun a => hpoly _ _ a.2)
  refine hJ.trans (iSup_le fun ev => ?_)
  classical
  refine le_iSup_of_le (fun k P => if h : HkIdx i k P then ev ⟨(k, P), h⟩ else 0) (inf_le_inf_right _ ?_)
  unfold Eigsp
  refine le_iInf fun k => le_iInf fun P => le_iInf fun h => ?_
  refine (iInf_le _ ⟨(k, P), h⟩).trans ?_
  simp only [dif_pos h]
  exact le_rfl

end GlobalTheory.GoodSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeIndex_sum_bound : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  first | exact @GlobalTheory.InertIdx.indexSum_inert | exact GlobalTheory.InertIdx.indexSum_inert | (intros; apply GlobalTheory.InertIdx.indexSum_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfInnerEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

theorem ops_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∃ B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) ∧ (∀ γ, ‖B γ‖ ≤ 1) ∧ B 1 = 1 ∧ ∀ γ k, k ∈ GlobalTheory.UpInj.KR R i → B (γ * k) = B γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL
  choose B hBn hBp using fun γ : GfC (Wc D i) => hTL.2.2.1 γ γ.2
  refine ⟨B, fun γ x y => hBp γ x y, hBn, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp 1 x y, ContinuousLinearMap.one_apply]
    exact hTL.2.2.2.2.2 x y
  · intro γ k hk
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp, ← hBp]
    have := hTL.2.2.2.1 γ γ.2 1 (Subgroup.one_mem _) k (Subgroup.mem_subgroupOf.1 hk) x y
    rwa [one_mul] at this

theorem coef_mult_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T), FinMult R i t → LocSmall R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ v (g h : GfC (Wc D i)), GlobalTheory.UpInj.cf (Wc D i) v g = 1 → GlobalTheory.UpInj.cf (Wc D i) v h = h → coef R i t μ 𝓕 ((g * h : GfC (Wc D i)) : GA D (Wc D i)) = coef R i t μ 𝓕 g * coef R i t μ 𝓕 h) ∧ ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (GfC (Wc D i))), (∀ g ∈ C, GlobalTheory.UpInj.cf (Wc D i) v g = g ∧ g ∉ GlobalTheory.UpInj.KR R i) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ GlobalTheory.UpInj.KR R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hFM hLS μ 𝓕 hμ
  refine ⟨fun v g h hg hh => ?_, ?_⟩
  · exact hFM μ 𝓕 hμ v _ (GlobalTheory.UpInj.isFinIdem_fE v) g g.2 (GlobalTheory.UpInj.trivAt_of_cf_eq_one _ v g hg) h
      ((GlobalTheory.UpInj.cf_eq_self_iff _ v h).1 hh)
  · obtain ⟨s, hs, hs1, hsb⟩ := hLS μ 𝓕 hμ
    refine ⟨s, hs, hs1, fun v C hC hCd => ?_⟩
    have := hsb v _ (GlobalTheory.UpInj.isFinIdem_fE v) (C.map (Function.Embedding.subtype _)) ?_ ?_
    · simpa [Finset.sum_map] using this
    · intro g hg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      exact ⟨(GlobalTheory.UpInj.cf_eq_self_iff _ v g).1 (hC g hgC).1, fun h => (hC g hgC).2 (Subgroup.mem_subgroupOf.2 h)⟩
    · intro g hg g' hg' hgg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      obtain ⟨g', hgC', rfl⟩ := Finset.mem_map.1 hg'
      refine congrArg _ (hCd g hgC g' hgC' (Subgroup.mem_subgroupOf.2 ?_))
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgg

set_option maxHeartbeats 1000000 in

theorem coef_biinv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → VecNe R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ g k k', k ∈ levW R i → k' ∈ levW R i → coef R i t μ 𝓕 (k * g * k') = coef R i t μ 𝓕 g) ∧ coef R i t μ 𝓕 1 = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hVN μ 𝓕 hμ
  have hv : ∀ k ∈ levW R i, R.ωP i t (1, k) (R.vP i t) = R.vP i t := fun k hk => by
    have := hLF k hk 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hW := hL.thP.ωP i t
  refine ⟨fun g k k' hk hk' => ?_, GlobalTheory.RawLift.Model.coef_one R i t hVN μ 𝓕 hμ⟩
  rw [GlobalTheory.RawLift.Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk']
  unfold coef
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  calc thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.vP i t)
      = thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.ωP i t (1, k) (R.vP i t)) := by rw [hv k hk]
    _ = thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) :=
      GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hμ (1, k) _ _ (hW.om_pres _ _ hth) hth

theorem injective_of_inner_eq {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : H →ₗ[ℂ] E) (W : H →L[ℂ] H) (a0 : ℝ) (ha0 : 0 < a0)
    (key : ∀ x y, ⟪L x, L y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ) (hW : Function.Injective W) : Function.Injective L := by
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have sym : ∀ x y, ⟪x, W y⟫_ℂ = ⟪W x, y⟫_ℂ := by
    intro x y
    have h2 : (a0 : ℂ) * ⟪x, W y⟫_ℂ = (a0 : ℂ) * ⟪W x, y⟫_ℂ := by
      rw [← key, ← inner_conj_symm, key, map_mul, Complex.conj_ofReal, inner_conj_symm]
    exact mul_left_cancel₀ ha0' h2
  intro x x' hxx'
  have hz : L (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  have h3 := key (x - x') (W (x - x'))
  rw [hz, inner_zero_left] at h3
  have h4 : ⟪x - x', W (W (x - x'))⟫_ℂ = 0 := (mul_eq_zero.1 h3.symm).resolve_left ha0'
  rw [sym] at h4
  have hWz : W (x - x') = 0 := inner_self_eq_zero.1 h4
  exact sub_eq_zero.1 (hW (hWz.trans (map_zero W).symm))

set_option maxHeartbeats 4000000 in
theorem upInj_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → LevProd R i → TransLaws R i → UpInj R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hFS hFM hLF hVN hLS _ hTL
  classical
  obtain ⟨⟨p, hp⟩, -⟩ := (hL.thP.vP i t).1.2.norm
  obtain ⟨hinv, h1⟩ := coef_biinv D G Pl0 T A Ks R F hL i t hLF hVN p.1 p.2 hp
  obtain ⟨hmul, s, hs, hs1, hsm⟩ := coef_mult_small D G Pl0 T A Ks R i t hFM hLS p.1 p.2 hp
  obtain ⟨B, hB, hBn, hB1, hBK⟩ := ops_exist D G Pl0 T A Ks R i hTL
  obtain ⟨hrep, hhk⟩ := GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity D G Pl0 T A Ks R i hTL B hB
  let a : GfC (Wc D i) → ℂ := fun g => coef R i t p.1 p.2 g
  have hmem := GlobalTheory.UpInj.kr_mem_iff R i
  have hfin := GlobalTheory.UpInj.kr_finite R i
  have hidem : ∀ v g, GlobalTheory.UpInj.cf (Wc D i) v (GlobalTheory.UpInj.cf (Wc D i) v g) = GlobalTheory.UpInj.cf (Wc D i) v g :=
    fun v g => GlobalTheory.UpInj.cf_cf (Wc D i) v g
  have horth : ∀ v w g, v ≠ w → GlobalTheory.UpInj.cf (Wc D i) w (GlobalTheory.UpInj.cf (Wc D i) v g) = 1 :=
    fun v w g h => GlobalTheory.UpInj.cf_orth (Wc D i) h g
  obtain ⟨e, he⟩ := GlobalTheory.T.quotient_equiv_restrictedComponentFamilies _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) hmem hfin hidem horth
  have ha_bi : ∀ g k k', k ∈ GlobalTheory.UpInj.KR R i → k' ∈ GlobalTheory.UpInj.KR R i → a (k * g * k') = a g := by
    intro g k k' hk hk'
    exact hinv g k k' (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hk')
  have ha_right : ∀ g k, k ∈ GlobalTheory.UpInj.KR R i → a (g * k) = a g := by
    intro g k hk
    have := ha_bi g 1 k (Subgroup.one_mem _) hk
    rwa [one_mul] at this
  have hfac := GlobalTheory.T.rightInvariant_mul_eq_finprod_components _ _ _ _ a hmem hfin hidem horth ha_right h1 hmul
  have hloc := fun v => GlobalTheory.T.hasSum_localEulerFactor_heckeOperators _ (GlobalTheory.UpInj.KR R i) (GlobalTheory.UpInj.cf (Wc D i) v) _ a B (s v) (hidem v) ha_bi hBK hBn
    (hsm v) (hrep v) (hhk v)
  obtain ⟨W, hWi, hW⟩ := GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) _ a B s e he hmem hidem horth ha_right h1 hfac
    hBn hB1 hBK hs hs1 hsm hloc
  intro th hth
  obtain ⟨a0, ha0, hsum⟩ := hFS th hth p.1 p.2 hp
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have key : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ := by
    intro x y
    have h2 := (hW x y).mul_left (a0 : ℂ)
    have e : (fun q : GfC (Wc D i) ⧸ GlobalTheory.UpInj.KR R i => (a0 : ℂ) * (a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ)) =
        fun q => (a0 : ℂ) * (coef R i t p.1 p.2 (Quotient.out q : GfC (Wc D i)) *
          trPair R i (Quotient.out q : GfC (Wc D i)) x y) := by
      funext q; rw [hB]
    rw [e] at h2
    exact (hsum x y).unique h2
  exact injective_of_inner_eq _ W a0 ha0 key hWi

end GlobalTheory.UpInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDZHeckeGen
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum GlobalTheory.DZero

namespace GlobalTheory.DZeroHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsDZType (π₀ : IrrGL k) {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀]
    (σ : Representation ℂ (GL (Fin π₀.1) 𝓀[k]) W₀) : Prop :=
  FiniteDimensional ℂ W₀ ∧ σ.IsIrreducible ∧ FinCusp σ ∧ ∃ j : W₀ →ₗ[ℂ] π₀.2.rep.V, HasType π₀.rep σ j

variable {d t N : ℕ}

abbrev dzBlocks (hN : ∑ _i : Fin t, d = N) : (Σ _a : Fin t, Fin d) ≃ Fin N :=
  stdBlocks (fun _ : Fin t => d) hN

variable (k) in

def dzJ (hN : ∑ _i : Fin t, d = N) : Subgroup (KO k (Fin N)) :=
  (parahoric k (dzBlocks hN)).subgroupOf (KO k (Fin N))

variable (k) in

def dzJIncl (hN : ∑ _i : Fin t, d = N) : dzJ k hN →* parahoric k (dzBlocks hN) :=
  (((KO k (Fin N)).subtype).comp (dzJ k hN).subtype).codRestrict _ fun x => x.2

def dzTau {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) : Representation ℂ (dzJ k hN) (PiTensorProduct ℂ fun _a : Fin t => W₀) :=
  (piTensor fun _a : Fin t => σ).comp ((parahoricProj k (dzBlocks hN)).comp (dzJIncl k hN))

def dzPerm (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Equiv.Perm (Fin N) :=
  if h : i + 1 < t then
    ((dzBlocks hN).symm.trans (Equiv.sigmaCongrLeft (β := fun _ : Fin t => Fin d) (Equiv.swap (⟨i, by omega⟩ : Fin t) ⟨i + 1, h⟩))).trans (dzBlocks hN)
  else 1

variable (k) in

def dzW (hN : ∑ _i : Fin t, d = N) (i : ℕ) : KO k (Fin N) :=
  toKO k (Fin N) ((Matrix.permMatrixHom (R := 𝒪[k])).toHomUnits (dzPerm hN i))

variable (k) in

def dzCoset (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Set (KO k (Fin N)) :=
  {g | ∃ a b : dzJ k hN, g = (a : KO k (Fin N)) * dzW k hN i * b}

def IsDZHeckeGen {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) (q : ℕ) (i : ℕ) (T : Module.End ℂ (indSpace (dzJ k hN) (dzTau σ hN))) : Prop :=
  (∀ κ : KO k (Fin N), T * ind (dzJ k hN) (dzTau σ hN) κ = ind (dzJ k hN) (dzTau σ hN) κ * T) ∧
    (T - (q : ℂ) • 1) * (T + 1) = 0 ∧
    ∀ f : indSpace (dzJ k hN) (dzTau σ hN), (∀ g ∈ dzCoset k hN i, f.1 g = 0) → (T f).1 1 = 0

variable (k) in

def dzQ (d : ℕ) : ℕ := resCard k ^ d

def dzT {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Module.End ℂ (indSpace (dzJ k hN) (dzTau σ hN)) :=
  Classical.epsilon (IsDZHeckeGen σ hN (dzQ k d) i)

end GlobalTheory.DZeroHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndependeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_automorphismConjugates_of_numberField_independent_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) → Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  first | exact @GlobalTheory.ConjSpan.span_conj_eq_top | exact GlobalTheory.ConjSpan.span_conj_eq_top | (intros; apply GlobalTheory.ConjSpan.span_conj_eq_top <;> assumption)
end

