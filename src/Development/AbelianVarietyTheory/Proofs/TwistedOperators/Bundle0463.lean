import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add, map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  refine ⟨GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
    exact Submodule.map_comap_le _ _
  · rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc, hx⟩ := exists_smul_mem L (y := ι x) (hsp ▸ Submodule.mem_sup_left ⟨x, rfl⟩)
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E c ≠ 0 := by simpa using hc
    have : x = (algebraMap (𝓞 D.host.E) D.host.E c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul D.host.E c, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (ι.restrictScalars (𝓞 D.host.E)) (c • x) ∈ L
    rw [map_smul]
    exact hx
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add, map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWittTowerIntertwinesLeviWeilRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped GlobalTheory.MixModel

namespace GlobalTheory.LeviScalar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem proj_mul_mt_inv (V V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) :
    HMul.hMul ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) (mt V m⁻¹) =
      HMul.hMul (mt V' g'⁻¹) ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) := by
  have hadj : adj D B = Bᴴ := GlobalTheory.MixModel.cT_sig B
  have hP : (V'.gram⁻¹ * adj D B * V.gram).map (incA D) =
      GlobalTheory.MixModel.giA V' * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
    rw [hadj]
    change GlobalTheory.MixModel.rat (V'.gram⁻¹ * Bᴴ * V.gram) = _
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_conjTranspose]
    rfl
  have hB' : mt V m * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B * mt V' g' := hB
  have key : GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.adj (mt V m) =
      GlobalTheory.MixModel.adj (mt V' g') * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) := by
    rw [← GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.adj_mul, hB']
  rw [hP, GlobalTheory.MixModel.mt_inv, GlobalTheory.MixModel.mt_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.gA_giA_cancel]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B)), key, Matrix.mul_assoc]

theorem actO_midPart (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) (h : GA D W) (x : WO V' W) :
    actO V W m h (midPart V V' W B x) = midPart V V' W B (actO V' W g' h x) := by
  have hq := proj_mul_mt_inv V V' B g' m hB
  unfold midPart
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq]
  generalize (V'.gram⁻¹ * adj D B * V.gram).map (incA D) = P at hq ⊢
  simp only [Matrix.mul_assoc]
  rw [hq]

theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq, inv_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  ext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem absE_ne_zero (u : (AE D)ˣ) : GlobalTheory.Doubling.absE D.host.F D.host.E u ≠ 0 := ((Group.isUnit u).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero

theorem detPow_pos {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  exact Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))) _

theorem enorm_inv_detPow_sq {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) :
    ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ ^ 2 *
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ n = 1 := by
  have ht : (0 : ℝ) < (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))
  have hd : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := detPow_pos a n
  have hsq : (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n) ^ 2 =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ n := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast _ n]
    congr 1
    push_cast
    ring
  have hn : ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ = ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hd.le]
  rw [hn, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (inv_nonneg.2 hd.le),
    ← ENNReal.ofReal_pow ht.le, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hd.le) _), ← hsq, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hd.ne'), ENNReal.ofReal_one]

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := fun hf hg => GlobalTheory.OrientedHeis.theta_add hf hg
  smul_mem' := fun c _ hf => GlobalTheory.OrientedHeis.theta_smul c hf

theorem eq_zero_of_lintegral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  apply GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (GlobalTheory.ThetaSchurBdd.integrable_sq hψ hcv.2.2 hf).aestronglyMeasurable]
  have h2 : ∫⁻ w in 𝓕, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    congr 1
    funext w
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h2, h0, ENNReal.toReal_zero]

theorem main : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ h : GA D W, ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) = ((c : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)) • ω' (g', h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ 𝓨 hcv a g' m hC hB h
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hcv
  have hheis := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1
  obtain ⟨μ', 𝓕', hcv'⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  rw [← GlobalTheory.MixModel.ratL_eq] at hcv'

  let Θ := thetaSpace ψ V W
  let R : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    { toFun := fun f => res V V' W C B μ 𝓨 f
      map_add' := fun f g => by
        funext x
        show ∫ y in 𝓨, ((f : WO V W → ℂ) + g) (isoPart V W C y + midPart V V' W B x) ∂μ =
          (∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ) +
            ∫ y in 𝓨, (g : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.add_apply]
        exact integral_add ((hres.1 f f.2).1 x) ((hres.1 g g.2).1 x)
      map_smul' := fun c f => by
        funext x
        show ∫ y in 𝓨, (c • (f : WO V W → ℂ)) (isoPart V W C y + midPart V V' W B x) ∂μ =
          c * ∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.smul_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  let Φ : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    R ∘ₗ (ω (m, h)).restrict (p := Θ) (q := Θ) (fun f hf => hω.om_pres (m, h) f hf)

  have hker : LinearMap.ker R ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have hf0 : res V V' W C B μ 𝓨 f = 0 := hf
    have hθ : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
      (hres.1 _ (hω.om_pres (m, h) f f.2)).2.1
    have hsq := GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ' 𝓕' hcv'.1 hcv'.2.1 a g' m hC hB h f f.2
    rw [hf0] at hsq
    simp only [Pi.zero_apply, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      MeasureTheory.lintegral_const, zero_mul, mul_zero] at hsq
    exact eq_zero_of_lintegral hψ hcv' hθ hsq

  let N₀ : LinearMap.range R →ₗ[ℂ] (WO V' W → ℂ) :=
    (LinearMap.ker R).liftQ Φ hker ∘ₗ R.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Nf, hN⟩ := LinearMap.exists_extend N₀
  have hNf : ∀ f, IsThetaFunO ψ V W f → Nf (res V V' W C B μ 𝓨 f) = res V V' W C B μ 𝓨 (ω (m, h) f) := by
    intro f hf
    let F : Θ := ⟨f, hf⟩
    have e1 : Nf (R F) = N₀ ⟨R F, LinearMap.mem_range_self R F⟩ := by
      rw [← hN]
      rfl
    show Nf (R F) = Φ F
    rw [e1]
    show (LinearMap.ker R).liftQ Φ hker (R.quotKerEquivRange.symm ⟨R F, LinearMap.mem_range_self R F⟩) = Φ F
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

  let d : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.2 (detPow_pos a W.rank).ne'
  let M : Module.End ℂ (WO V' W → ℂ) := d⁻¹ • (ω' (g'⁻¹, h⁻¹) * Nf)
  have hMres : ∀ f, IsThetaFunO ψ V W f →
      M (res V V' W C B μ 𝓨 f) = d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) := by
    intro f hf
    show d⁻¹ • ω' (g'⁻¹, h⁻¹) (Nf (res V V' W C B μ 𝓨 f)) = _
    rw [hNf f hf]
  have hθω : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
    fun f hf => (hres.1 _ (hω.om_pres (m, h) f hf)).2.1
  have hM1 : ∀ f', IsThetaFunO ψ V' W f' → IsThetaFunO ψ V' W (M f') := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    exact GlobalTheory.OrientedHeis.theta_smul _ (hω'.om_pres _ _ (hθω f hf))
  have hM2 : ∀ x f', IsThetaFunO ψ V' W f' → M (heisO ψ V' W x f') = heisO ψ V' W x (M f') := by
    intro x f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    have hx : heisO ψ V' W x (res V V' W C B μ 𝓨 f) =
        res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) :=
      (GlobalTheory.TowerRestrict.res_heis_mid hs μ 𝓨 f x).symm
    rw [hx, hMres _ (hheis _ _ hf), hMres f hf, hω.om_heis m h _ f hf, actO_midPart V V' W B g' m hB h x,
      GlobalTheory.TowerRestrict.res_heis_mid hs, hω'.om_heis _ _ _ _ (hθω f hf), actO_inv_actO, heisO_smul]
  have hM3 : ∀ (μ₀ : Measure (WO V' W)) (𝓕₀ : Set (WO V' W)), μ₀.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V') 𝓕₀ μ₀ → ∀ f', IsThetaFunO ψ V' W f' →
      ∫⁻ w in 𝓕₀, ‖M f' w‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕₀, ‖f' w‖ₑ ^ 2 ∂μ₀ := by
    intro μ₀ 𝓕₀ hH hF f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    have hpt : ∀ w, ‖(d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f))) w‖ₑ ^ 2 =
        ‖d⁻¹‖ₑ ^ 2 * ‖ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) w‖ₑ ^ 2 := by
      intro w
      rw [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top),
      hω'.om_unit μ₀ 𝓕₀ hH hF _ _ (hθω f hf),
      GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ₀ 𝓕₀ hH hF a g' m hC hB h f hf,
      ← mul_assoc, enorm_inv_detPow_sq, one_mul]
  obtain ⟨c₀, hc₀, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ V' W M hM1 hM2 hM3
  have hinv : ∀ X, ω' (g', h) (ω' (g'⁻¹, h⁻¹) X) = X := by
    intro X
    have e : ω' (g', h) * ω' (g'⁻¹, h⁻¹) = 1 := by
      rw [← map_mul]
      show ω' ((g', h) * (g', h)⁻¹) = 1
      rw [mul_inv_cancel, map_one]
    exact congrArg (fun L : Module.End ℂ (WO V' W → ℂ) => L X) e
  refine ⟨⟨c₀, mem_sphere_zero_iff_norm.2 hc₀⟩, fun f hf => ?_⟩
  have e2 : d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) = c₀ • res V V' W C B μ 𝓨 f := by
    rw [← hMres f hf]
    exact hM _ (hres.1 f hf).2.1
  have e3 : d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f) = c₀ • ω' (g', h) (res V V' W C B μ 𝓨 f) := by
    have e4 := congrArg (ω' (g', h)) e2
    rwa [map_smul, map_smul, hinv] at e4
  calc res V V' W C B μ 𝓨 (ω (m, h) f) = d • (d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f)) := by
        rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    _ = _ := by
        rw [e3, smul_smul]
        congr 1
        exact mul_comm _ _

end GlobalTheory.LeviScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AdjSrcZero

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  obtain ⟨⟨hAA, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  intro h0
  apply hAA
  rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
  intro x hx
  have h1 : star x ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  have h2 := h0 _ h1
  simpa using congrArg star h2

theorem AAbar_mul_st (G : GridData L sc) :
    D.host.AAbar * (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) = D.host.AA * shiftId G := by
  have hA := AAbar_ne_zero D
  simp only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]
  calc _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA *
        (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem star_smul_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ}
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA,
    ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀,
    star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  intro D T L sc G n Λ₀ a ha s hs
  obtain ⟨⟨-, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  have key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
    intro b hb y hy
    refine FractionalIdeal.mul_induction_on (C := fun b => b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_
    · intro i hi j hj
      refine Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩
      rw [smul_smul]
    · intro x z hx hz
      rw [add_smul]
      exact add_mem hx hz
  have hsa : star a ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  unfold idLat at hs
  refine Submodule.span_induction (p := fun z _ => star a • z ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨i, hi, y, hy, rfl⟩
    rw [smul_smul]
    exact key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy
  · simp
  · intro x z _ _ hx hz
    rw [smul_add]
    exact add_mem hx hz
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.AdjSrcZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end

