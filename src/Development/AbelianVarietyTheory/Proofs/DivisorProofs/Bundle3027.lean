import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0998
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuous
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoCont

variable {F : Type} [Field F] [NumberField F]

def mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : AF F :=
  (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) b : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evI_mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : evI F (mkA a b) = a := by
  simp [evI, mkA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : (κ → Af F) → ℂ) :
    pureA F f (a + b) = pureA F f a + pureA F f b := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (a : (κ → Af F) → ℂ) :
    pureA F f (c • a) = c • pureA F f a := by
  funext x; simp [pureA]; ring

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_mkA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a : (κ → Af F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : pureA F f a (fun i => mkA (y i) (z i)) = f y * a z := by
  simp only [pureA]
  congr 1
  congr 1
  funext i
  exact evI_mkA (y i) (z i)

theorem thetaSum_finset_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i ∈ s, Φ i ∈ schA F κ) : thetaSum F (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaSum F (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (h a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

open scoped Classical in

theorem soCont (hP : KP) : SoCont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair m φ f u hconv hSo hSoLim h
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  have hU := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    hPair.weil.isUSplitting.pres
  haveI := hPair.good.haar
  have hfin : M.μ M.dom < ⊤ := GlobalTheory.UnitaryVol.measure_fundDom_lt_top hP.siegelSetUnitary hPair.base.cm
    (GlobalTheory.UnitaryVol.isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hPair.base.cm) hPair.herm) hPair.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩

  let So := M.So B.ψ B.τ₁
  let T' : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) :=
    { carrier := {a | ∀ g : SInf F (Fin n × Fin d), pureA F g a ∈ So}
      add_mem' := fun ha hb g => by rw [pureA_add]; exact So.add_mem (ha g) (hb g)
      zero_mem' := fun g => by rw [pureA_zero]; exact So.zero_mem
      smul_mem' := fun c a ha g => by rw [pureA_smul]; exact So.smul_mem c (ha g) }
  let T := SB (Fin n × Fin d → Af F) ⊓ T'

  have hslice : ∀ Φ ∈ So, ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      (fun z : Fin n × Fin d → Af F => Φ (fun i => mkA (y i) (z i))) ∈ T' := by
    intro Φ hΦ y
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, ψ, h1, h2, h3, rfl⟩ := hΦ
      let a : (Fin n × Fin d → Af F) → ℂ := fun z => ∏ᶠ v, ψ v fun i => evFin F v (mkA 0 (z i))
      have e1 : (fun z : Fin n × Fin d → Af F => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g ψ (fun i => mkA (y i) (z i))) = g y • a := by
        funext z
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, a]
        congr 1
        congr 1
        funext i
        exact evI_mkA (y i) (z i)
      have e2 : ∀ g' : SInf F (Fin n × Fin d), pureA F g' a = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' ψ := fun g' => by
        funext x
        rfl
      rw [e1]
      refine T'.smul_mem _ fun g' => ?_
      rw [e2]
      exact Submodule.subset_span ⟨g', ψ, h1, h2, h3, rfl⟩
    | zero =>
      have e0 : (fun z : Fin n × Fin d → Af F => (0 : (Fin n × Fin d → AF F) → ℂ) (fun i => mkA (y i) (z i))) = 0 := rfl
      rw [e0]
      exact T'.zero_mem
    | add Φ Ψ _ _ hΦ hΨ => exact T'.add_mem hΦ hΨ
    | smul c Φ _ hΦ => exact T'.smul_mem c hΦ

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl T
  have hdec : ∀ j, ∃ t ∈ T, ∃ c ∈ C, t + c = φ j := fun j =>
    Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top)
  choose t htT c hcC htc using hdec
  have hcSB : ∀ j, c j ∈ SB (Fin n × Fin d → Af F) := fun j => by
    have : c j = φ j - t j := by rw [← htc j]; abel
    rw [this]; exact Submodule.sub_mem _ (hconv j).1 (htT j).1

  have hred : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) := by
    intro w hw
    have e : ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) + ∑ j, pureA F (w j) (c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← pureA_add, htc j]
    have hΨ : ∑ j, pureA F (w j) (c j) ∈ So := by
      have : ∑ j, pureA F (w j) (c j) = ∑ j, pureA F (w j) (φ j) - ∑ j, pureA F (w j) (t j) := by
        rw [e]; abel
      rw [this]
      exact So.sub_mem hw (So.sum_mem fun j _ => (htT j).2 (w j))
    have h0 : ∀ y, ∑ j, w j y • c j = 0 := by
      intro y
      have h1 : ∑ j, w j y • c j ∈ T := by
        refine ⟨SB _ |>.sum_mem fun j _ => (SB _).smul_mem _ (hcSB j), ?_⟩
        have := hslice _ hΨ y
        have e' : (fun z : Fin n × Fin d → Af F => (∑ j, pureA F (w j) (c j)) (fun i => mkA (y i) (z i))) =
            ∑ j, w j y • c j := by
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureA_mkA]
        rwa [e'] at this
      have h2 : ∑ j, w j y • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (hcC j)
      have := hC.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact (Submodule.mem_bot ℂ).1 this
    rw [e, add_eq_left]
    funext x
    have := congrFun (h0 fun i => evI F (x i)) (fun i => (x i).2)
    simpa [pureA, Finset.sum_apply, evI] using this

  have hmem : ∀ (a : (Fin n × Fin d → Af F) → ℂ), a ∈ SB (Fin n × Fin d → Af F) → ∀ g : SInf F (Fin n × Fin d),
      pureA F g a ∈ schA F (Fin n × Fin d) := fun a ha g => Submodule.subset_span ⟨g, a, ha, rfl⟩
  have hmeas : ∀ Φ ∈ schA F (Fin n × Fin d),
      AEStronglyMeasurable (fun x => theta om Φ x h) (M.μ.restrict M.dom) := by
    intro Φ hΦ
    haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
    exact ((hB.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hbd : ∀ a ∈ T, ∃ (C0 : ℝ) (k0 : ℕ), 0 ≤ C0 ∧ ∀ (g : SInf F (Fin n × Fin d)) x,
      ‖theta om (pureA F g a) x h‖ ≤ C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0 := by
    intro a ha
    obtain ⟨C0, k0, hC0⟩ := hU a ha.1 ha.2 0
    refine ⟨max C0 0, k0, le_max_right _ _, fun g x => ?_⟩
    have := hC0 g x h
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have hint : ∀ a ∈ T, ∀ g : SInf F (Fin n × Fin d),
      Integrable (fun x => theta om (pureA F g a) x h) (M.μ.restrict M.dom) := by
    intro a ha g
    obtain ⟨C0, k0, -, hC0⟩ := hbd a ha
    exact Integrable.mono' (integrable_const (C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0))
      (hmeas _ (hmem a ha.1 g)) (ae_of_all _ fun x => hC0 g x)
  have hcont : ∀ a ∈ T, ∀ (v : ℕ → SInf F (Fin n × Fin d)) (g0 : SInf F (Fin n × Fin d)), Tendsto v atTop (𝓝 g0) →
      Tendsto (fun k => M.I om (pureA F (v k) a) h) atTop (𝓝 (M.I om (pureA F g0 a) h)) := by
    intro a ha v g0 hv
    obtain ⟨C0, k0, hC0p, hC0⟩ := hbd a ha
    have hsem : ∀ᶠ k in atTop, semK (Fin n × Fin d) k0 (v k) ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
      have h1 := ((schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds' v g0).1 hv
        (Finset.Iic (k0, k0)) 1 one_pos
      filter_upwards [h1] with k hk
      calc semK (Fin n × Fin d) k0 (v k) = semK (Fin n × Fin d) k0 ((v k - g0) + g0) := by rw [sub_add_cancel]
        _ ≤ semK (Fin n × Fin d) k0 (v k - g0) + semK (Fin n × Fin d) k0 g0 := map_add_le_add _ _ _
        _ ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
          have : semK (Fin n × Fin d) k0 (v k - g0) < 1 := hk
          linarith
    simp only [Model.I]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => C0 * (semK (Fin n × Fin d) k0 g0 + 1) * (ht h : ℝ) ^ k0)
      (Eventually.of_forall fun k => hmeas _ (hmem a ha.1 (v k))) ?_ (integrable_const _) ?_
    · filter_upwards [hsem] with k hk
      refine ae_of_all _ fun x => (hC0 (v k) x).trans ?_
      gcongr
    · exact ae_of_all _ fun x => ((hB.2 a ha.1 x h).tendsto g0).comp hv

  have hI : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      M.I om (∑ j, pureA F (w j) (φ j)) h = ∑ j, M.I om (pureA F (w j) (t j)) h := by
    intro w hw
    rw [hred w hw]
    simp only [Model.I]
    rw [← integral_finset_sum _ fun j _ => hint (t j) (htT j) (w j)]
    congr 1
    funext x
    simp only [theta]
    rw [map_sum]
    exact thetaSum_finset_sum _ _ fun j _ => hpres _ _ (hmem _ (htT j).1 (w j))
  rw [hI f hSoLim]
  refine Tendsto.congr (fun k => (hI (u k) (hSo k)).symm) ?_
  exact tendsto_finset_sum _ fun j _ => hcont (t j) (htT j) (fun k => u k j) (f j) (hconv j).2

end GlobalTheory.ThKSoCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointCongruentTermSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval

theorem value_sub_sum_mem_hRed : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  intro R _ _ I D A G _ _ U h g hF f t e k hT σ fs hE x hx a ha
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e (𝟙_ (Over (Sp R)))).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  have hs1 : s ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e := pullback.lift_fst _ _ _
  have hs2 : s ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨hb, hχ⟩ := hF e
  have hp : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
    rw [← hs2, Category.assoc, ← hb, ← Category.assoc, hs1]
  have hf : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left := hRed_fst h e
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ fs hE
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT' => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, GlobalTheory.ExpansionValueZero.cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (hRed I h e) z J hJ
  have h₂ := h₁ (J' (hRed I h e ≫ fGl I G e)) (hJ' (hRed I h e ≫ fGl I G e))
  have hsv : sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e)) =
      cst (thick R I e) z x * (val f (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ h.left)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (hRed I h e) z J = val (g.s α) (thick R I e) z J := fun α => by
    have e₁ := (val_pull hJ (tG U e α) ((Over.pullback (thick R I e)).map h).left s).symm
    have e₂ := (val_corr hJ (hχ α) s).symm
    have e₃ := val_pull hJ (g.s α) (fstG I e (𝟙_ (Over (Sp R)))).left s
    rw [hs2] at e₁
    rw [hs1] at e₃
    exact e₁.trans (e₂.trans e₃)
  have hg : ∀ α, sval (fs α) (hRed I h e ≫ pGl U e) z J = sval (fs α) (thick R I e ≫ g.b.left) z J := fun α => by
    rw [hp]
  have hTR := hT _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at hTR
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT' (fun α _ hα => (ha α _ _ z J hJ).symm.trans
    (by rw [← hg, h₀ α hα, zero_mul, zero_mul]))]
  have L₁ : cst (thick R I e) z x * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val =
      ((wv U e (hRed I h e) z (J (hRed I h e ≫ pGl U e)) (J' (hRed I h e ≫ fGl I G e)) ^ k).val *
        sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e))) *
        (val t (thick R I e) z J ^ k).val := by
    rw [hsv, ← hTR]
    simp only [mul_pow, Units.val_mul]
    ring
  rw [L₁, h₂, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ht, hg]
  exact ha α _ _ z J hJ

end GlobalTheory.Poinc.IntEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TupLe

variable {D : D7}

theorem isConjPl_div {P P' : Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') : Formalism.L2.DIV.IsConjPl P P' :=
  fun a b e => h a b (by rw [e, Formalism.BasicNotions.Examples₂.star_eq_conj])

theorem lev_isConjPl_iff {P P' : Pl D.host.E} : Lev.IsConjPl P P' ↔ P' = Formalism.L2.DIV.conjPl P := by
  refine ⟨fun h => (isConjPl_div (isConjPl_of_lev h)).eq_conjPl, ?_⟩
  rintro rfl
  have h : Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
  rwa [(isConjPl_div (isConjPl_of_lev h)).eq_conjPl] at h

theorem isConjPl_conjPl_divisor (P : Pl D.host.E) : Formalism.BasicNotions.IsConjPl D.host P (Formalism.L2.DIV.conjPl P) :=
  isConjPl_of_lev (lev_isConjPl_iff.2 rfl)

open Classical in

theorem disjoint_conj {X : Finset (Pl D.host.E)} (hX : SplitSet X) : Disjoint X (X.image Formalism.L2.DIV.conjPl) := by
  refine Finset.disjoint_left.2 fun P hP hQ => ?_
  obtain ⟨P₀, h0, rfl⟩ := Finset.mem_image.1 hQ
  have a1 : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P₀)) (Formalism.L2.DIV.conjPl P₀) :=
    GlobalTheory.MovedIdem.isIdemAt_conj (hX.isIdemAt h0) fun x => Iff.rfl
  have a2 := hX.mul_conj hP h0
  rw [idemAt_eq a1, a1.1.1] at a2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Formalism.L2.DIV.conjPl P₀).ne_bot
  refine (a1.2 x hx0).1 hx ?_
  rw [a2, zero_mul, map_zero]
  exact zero_mem _

open Classical in

theorem idem_add_cA {X : Finset (Pl D.host.E)} (hX : SplitSet X) :
    idem X + cA D (idem X) = idem (X ∪ X.image Formalism.L2.DIV.conjPl) := by
  rw [← idem_eq (GlobalTheory.RefDatumLev.isIdemSum_conjPl hX.isIdemSum), idem, idem, idem, Finset.sum_union (disjoint_conj hX)]

open Classical in

theorem idem_add_cA_eq {X Y : Finset (Pl D.host.E)} (hX : SplitSet X) (hY : SplitSet Y)
    (h : ∀ P, P ∈ X ∪ X.image Formalism.L2.DIV.conjPl ↔ P ∈ Y ∪ Y.image Formalism.L2.DIV.conjPl) :
    idem X + cA D (idem X) = idem Y + cA D (idem Y) := by
  rw [idem_add_cA hX, idem_add_cA hY]
  congr 1
  ext P
  exact h P

open Classical in

theorem mem_half_closure {ch : Set (Pl D.host.E)}
    (hch : ∀ P P', Formalism.BasicNotions.IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) {A B : Finset (Pl D.host.E)}
    (hcl : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ∈ A ∨ Formalism.L2.DIV.conjPl P ∈ B)
    (hne : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ≠ P) (P : Pl D.host.E) :
    P ∈ half ch A ∪ half ch B ∪ (half ch A ∪ half ch B).image Formalism.L2.DIV.conjPl ↔ P ∈ A ∨ P ∈ B := by
  have hY : ∀ P, P ∈ half ch A ∪ half ch B → P ∈ A ∨ P ∈ B := fun P h => by
    rcases Finset.mem_union.1 h with h | h
    exacts [Or.inl (mem_half.1 h).1, Or.inr (mem_half.1 h).1]
  have hmY : ∀ P, P ∈ A ∨ P ∈ B → P ∈ ch → P ∈ half ch A ∪ half ch B := fun P hP hc => by
    rcases hP with h | h
    exacts [Finset.mem_union_left _ (mem_half.2 ⟨h, hc⟩), Finset.mem_union_right _ (mem_half.2 ⟨h, hc⟩)]
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact hY P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      exact hcl P' (hY P' hP')
  · intro hP
    by_cases hc : P ∈ ch
    · exact Finset.mem_union_left _ (hmY P hP hc)
    · have hc' : Formalism.L2.DIV.conjPl P ∈ ch := by
        by_contra hc'
        exact hc ((hch P (Formalism.L2.DIV.conjPl P) (isConjPl_conjPl_divisor P) (hne P hP).symm).2 hc')
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨Formalism.L2.DIV.conjPl P, hmY _ (hcl P hP) hc', Formalism.L2.DIV.conjPl_conjPl P⟩)

theorem not_mem_of_coprime {P : Pl D.host.E} {l q : ℕ} (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (hc : Nat.Coprime l q) :
    (l : 𝓞 D.host.E) ∉ P.asIdeal := fun hl => by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have e : (u : 𝓞 D.host.E) * (l : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * (q : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hq)

open Classical in

theorem placesSt : PlacesSt := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm

end GlobalTheory.BigOn.Exp.TupLe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMonoOfHeightNefStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfIntersection_mono_of_height_nef : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  first | exact @GlobalTheory.HSNef.selfInter_mono | exact GlobalTheory.HSNef.selfInter_mono | (intros; apply GlobalTheory.HSNef.selfInter_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_pullback_abelian_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  first | exact @GlobalTheory.FactorOverOpen.factor_over_open | exact GlobalTheory.FactorOverOpen.factor_over_open | (intros; apply GlobalTheory.FactorOverOpen.factor_over_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpOverOfPolarizedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharpOver_of_polarized_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_baseChange | exact GlobalTheory.Poinc.sharpOver_baseChange | (intros; apply GlobalTheory.Poinc.sharpOver_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_polarization_unique_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u → GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' → ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  first | exact @GlobalTheory.Poinc.sharpOver_unique | exact GlobalTheory.Poinc.sharpOver_unique | (intros; apply GlobalTheory.Poinc.sharpOver_unique <;> assumption)
end

