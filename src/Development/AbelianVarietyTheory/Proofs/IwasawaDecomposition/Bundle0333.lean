import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0249
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

theorem coord_mem_smallSec (k : Type) [CommRing k] (N : ℕ) (a : Fin (N + 1)) :
    coord k N a ∈ (hermitianTwistingSheaf k N).smallSec := by
  intro σ y
  have e (a) : Weight.combVal (PSpace.str k N) σ (coord k N) 1 a = secVal _ σ (coord k N a) := by
    simp [Weight.combVal, Matrix.one_apply]
  refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := O1_isLB k N) (he := fun a => e a ▸ secVal_mem _)
    (h := Weight.noCommonZero_combVal (iSup_nonzeroLocus_coord k N) (M := 1) (by simp)) y)
  exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
    (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

theorem ringKrullDim_ringOfIntegers : ringKrullDim (𝓞 F) = 1 := by
  have h : Ring.KrullDimLE 1 (𝓞 F) := inferInstance
  refine le_antisymm (by exact_mod_cast Ring.krullDimLE_iff.1 h) ?_
  by_contra hlt
  have : Ring.KrullDimLE 0 (𝓞 F) := Ring.krullDimLE_iff.2 (by
    have h' : ringKrullDim (𝓞 F) ≤ 0 := Order.le_of_lt_succ (not_le.1 hlt)
    exact_mod_cast h')
  exact RingOfIntegers.not_isField F Ring.KrullDimLE.isField_of_isDomain

def projModel : TrueGeo.Model (proj F n) where
  X := PSpace (𝓞 F) n
  p := PSpace.str (𝓞 F) n
  ar := isArithVar_pspace (𝓞 F) (ringKrullDim_ringOfIntegers F) n
  j := (proj F n).ι ≫ baseChange n (algebraMap (𝓞 F) F)
  pb := by
    have H : IsPullback (proj F n).ι (proj F n).str (PSpace.str F n) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
    have := H.paste_horiz (isPullback_baseChange n (algebraMap (𝓞 F) F))
    rwa [Category.id_comp] at this

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ (M : TrueGeo.Model (proj F n)) (L : HermLB M.p) (Δ : (proj F n).Dv) (r : (L.B.pull M.j).ι → (proj F n).Fnˣ), Presents Δ (L.B.pull M.j) r ∧ (proj F n).inter (fun _ => Δ) = 1 ∧ ArInt.NefFib L ∧ ∀ x : M.X, ∃ s ∈ L.smallSec, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := by
  intro F _ _ n
  have hL := LB.isLB_pull (O1_isLB (𝓞 F) n) (projModel F n).j
  obtain ⟨r, hr⟩ := exists_isRatSec hL
  have hp := presents_divOfRatSec hL hr
  refine ⟨projModel F n, hermitianTwistingSheaf (𝓞 F) n, _, r, hp, ?_, ?_, fun x => ?_⟩
  · refine (Var.inter_congr fun _ => ?_).trans (inter_projHyp F n)
    refine hp.toPic_eq.trans (Eq.trans ?_ ((proj F n).presents_hyp _).toPic_eq.symm)
    refine (cls_pull (O1_isLB (𝓞 F) n) _ _).trans ((pull_comp _ _ _).trans ?_)
    refine Eq.trans (congrArg _ ?_) (cls_pull (O1_isLB F n) _ _).symm
    exact (cls_eq_iff (LB.isLB_pull (O1_isLB (𝓞 F) n) _) (O1_isLB F n)).2 (lbIso_pull_O1 n _)
  · have := Geo.Tor.isProper_str (𝓞 F) n
    exact nefFib_of_isAmpleLB (hermitianTwistingSheaf (𝓞 F) n) (GlobalTheory.isAmple_projective_O_one (𝓞 F) n)
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord (𝓞 F) n).ge (Opens.mem_top x))
    exact ⟨_, coord_mem_smallSec _ n a, ha⟩

end GlobalTheory.ProjModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CuspDeriv

theorem continuous_deriv_of_bounded {G : Type} [TopologicalSpace G] {f f₁ f₂ : G → ℝ → ℂ}
    (hf : ∀ t, Continuous fun g => f g t) (h₁ : ∀ g t, HasDerivAt (f g) (f₁ g t) t)
    (h₂ : ∀ g t, HasDerivAt (f₁ g) (f₂ g t) t) {B : ℝ} (hB : ∀ g t, ‖f₂ g t‖ ≤ B) : Continuous fun g => f₁ g 0 := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB g₀ 0)
  obtain ⟨h, h0, hh⟩ : ∃ h : ℝ, 0 < h ∧ (B + B) * h < ε :=
    ⟨ε / (B + B + 1), by positivity, by rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith⟩
  have hc : Continuous fun g => ‖f g h - f g₀ h‖ + ‖f g 0 - f g₀ 0‖ + (B + B) * h * h :=
    ((((hf h).sub continuous_const).norm).add ((hf 0).sub continuous_const).norm).add continuous_const
  have := (hc.tendsto g₀).eventually_lt_const (u := h * ε) (by simp only [sub_self, norm_zero, zero_add]; nlinarith)
  filter_upwards [this] with g hg
  have key := mul_norm_deriv_le (f := fun t => f g t - f g₀ t) (f₁ := fun t => f₁ g t - f₁ g₀ t)
    (f₂ := fun t => f₂ g t - f₂ g₀ t) (fun t => (h₁ g t).sub (h₁ g₀ t)) (fun t => (h₂ g t).sub (h₂ g₀ t)) h0.le
    (B := B + B) fun t _ => (norm_sub_le _ _).trans (add_le_add (hB g t) (hB g₀ t))
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (key.trans_lt hg) h0.le

theorem cuspForm_mem_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F,
    IsCuspForm θ V F → F ∈ Decay θ V := by
  intro hP D θ hθ V F ⟨ha, hc⟩
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hd : ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) → IsRapidDecay θ V (word θ V l F) :=
    isRapidDecay_foldr_Rder hP hθ ha.toIsAutFun ha.smooth ha.growth hc
  refine ⟨ha.smooth, ha.left, fun l hl => ⟨?_, hd l hl⟩⟩
  induction l with
  | nil => exact ha.cont
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (by simp [hq])
    have hs : word θ V l F ∈ SmFun θ V :=
      (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
        fun q hq => linOnSm_Rder (hl' q hq)).mem F ha.smooth
    obtain ⟨B, hB⟩ := (hd (p :: p :: l) (List.forall_mem_cons.2 ⟨hp, hl⟩)).bounded
    have := continuous_deriv_of_bounded (f := fun g t => word θ V l F (g * oneP θ V p.1 p.2 t))
      (fun t => (ih hl').comp (continuous_mul_const _)) (hasDerivAt_oneP hθ hp (hasDerivAt_Rder hs hp))
      (hasDerivAt_oneP hθ hp (hasDerivAt_Rder (Rder_mem hs hp) hp)) fun g t => hB _
    simp only [oneP_zero hθ, mul_one] at this
    exact this

end GlobalTheory.Mem.CuspDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobGarding

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) :
    ∃ φ', IsTest φ' ∧ ∀ w, word (trRep σ P) l (gard ε σ φ w) = gard ε σ φ' w := by
  induction l with
  | nil => exact ⟨φ, hφ, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨φ', h1, h2⟩ := ih fun Y hY => hl Y (by simp [hY])
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ' h1
    exact ⟨ψ X, (hψ X).1, fun w => by rw [word_cons, h2, (hψ X).2 (hl X (by simp))]⟩

theorem inner_word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G (trRep σ P)) (a : H) :
    ⟪a, word (trRep σ P) l (gard ε σ φ w)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪a, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hc := GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ l hl w hw
  have key : ∀ y : H, ⟪y, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • word (trRep σ P) l (σ (umat g) w) ∂(Formalism.REAL.muG ε)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    intro y
    rw [← integral_inner (hφ.integrable hc)]
    congr 1
    funext g
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
  rw [← key]
  congr 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint (gram_unit hP h) (isURepOn_trRep hP h hσ) hl hu
  rw [key, h2 _ (gard_mem hP h hσ hφ w), inner_gard hσ hφ]
  congr 1
  funext g
  rw [h2 _ (sigma_mem hP h hσ hw g.2)]

theorem sobCont_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ hℓ
  obtain ⟨m, ls, a, hls, hrep⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner n ε H σ P G hP h hσ ℓ hℓ
  refine ⟨fun φ hφ => ?_, fun w hw => ?_⟩
  · choose ψ _ hψ using fun i => word_gard hP h hσ hφ (ls i) (hls i)
    refine ⟨∑ i, ‖a i‖ * ∫ g : Formalism.REAL.UJ ε, |ψ i (umat g)| ∂(Formalism.REAL.muG ε), fun w => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hψ, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_gard_le hσ _ w) (norm_nonneg _))
  · have e : ∀ g : Formalism.REAL.UJ ε, ℓ (σ (umat g) w) = ∑ i, ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun g => hrep _ (sigma_mem hP h hσ hw g.2)
    have hc : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun i => continuous_const.inner (GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ (ls i) (hls i) w hw)
    simp only [e]
    refine ⟨continuous_finset_sum _ fun i _ => hc i, fun φ hφ => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w)]
    simp only [Finset.smul_sum]
    rw [integral_finset_sum _ fun i _ => hφ.integrable (hc i)]
    exact Finset.sum_congr rfl fun i _ => inner_word_gard hP h hσ hφ (ls i) (hls i) hw (a i)

end GlobalTheory.SobGarding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTopStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), Submodule.span (v.adicCompletion K) (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  first | exact @GlobalTheory.span_basis_image_adicCompletion_eq_top | exact GlobalTheory.span_basis_image_adicCompletion_eq_top | (intros; apply GlobalTheory.span_basis_image_adicCompletion_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

set_option maxHeartbeats 10000000 in

theorem span_liftForm_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB _ _ i t
  classical
  have hHV := hB.models.HV i t
  have hjV := hB.models.jV
  have hExt : (R.B.L i t).pres.ExtBij :=
    (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have key : (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      fun x => (R.cV i).ext ((R.B.L i t).pres.extL (GlobalTheory.OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) := by
    funext x
    exact congrArg (R.cV i).ext (hjV i t _)
  have hR : Set.range (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      (R.cV i).ext '' ((R.B.L i t).pres.extL ''
        {f | ∀ u : F.P0, A.leftGroupActionLift i t (u : G) f = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • f}) := by
    rw [key]
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ _).1 ⟨x, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ f).2 hf
      exact ⟨x, rfl⟩
  rw [hR, Submodule.span_image]
  ext Y
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range]
  have hs1 := GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation (W := (R.cV i).W) (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL (R.cV i).coef.ρ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (A.leftGroupActionLift i t)
    (R.B.L i t).pres (R.B.L i t).act_tie hExt F.P0 F.ψ0⁻¹
  have hs2a := GlobalTheory.T.base_level_adelic_type_implies_lift_law D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  have hs2b := GlobalTheory.T.lift_law_implies_adelic_extension_base_level D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    obtain ⟨hAd, hq⟩ := (hs1 Φ).1 hΦ
    refine ⟨?_, hs2b Φ hq⟩
    have h1 : Φ ∈ LinearMap.range (R.HV i t).e := by rw [hHV.2.1]; exact hAd
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨⟨y, rfl⟩, hlev⟩
    have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ y
    rw [hHV.2.1] at h1
    exact ⟨(R.HV i t).e y, (hs1 _).2 ⟨h1, hs2a _ hlev⟩, rfl⟩

end GlobalTheory.LiftSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMapStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | exact GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | (intros; apply GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroForms

theorem law0_choose_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V),
    (l0 u I.mu0).choose x = x := by
  intro B X I h l Z l0 u x
  apply (I.fm l u I.mu0).emb_inj 0
  rw [(l0 u I.mu0).choose_spec.2 x]
  show LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u I.mu0).symm ((I.fm l u I.mu0).emb 0 x) = _
  funext c
  rw [LinearEquiv.funCongrLeft_apply]
  show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u I.mu0).symm c) = _
  have hc : (I.eCls0 l u I.mu0).symm c = c :=
    (I.eCls0 l u I.mu0).symm_apply_eq.2 (GlobalTheory.T.eCls0_mu0_eq_self I h l u c).symm
  rw [hc]

end GlobalTheory.Mem.Col2.TC.MuZeroForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftPolar

theorem sesq_eq_of_diag {V : Type} [AddCommGroup V] [Module ℂ V] (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = B' v v) (f g : V) : B f g = B' f g := by
  have h1 := h (f + g)
  have h2 := h (f + Complex.I • g)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_I, h f, h g] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (B f g - B' f g - B g f + B' g f) * Complex.I_mul_I

theorem integral_mul_star_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (Θ : Submodule ℂ (X → ℂ)) (hm : ∀ f ∈ Θ, Measurable f) (hb : ∀ f ∈ Θ, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (M : Module.End ℂ (X → ℂ)) (hM : ∀ f ∈ Θ, M f ∈ Θ)
    (hn : ∀ f ∈ Θ, ∫⁻ x, ‖M f x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) (f f' : X → ℂ) (hf : f ∈ Θ) (hf' : f' ∈ Θ) :
    ∫ x, M f x * star (M f' x) ∂ν = ∫ x, f x * star (f' x) ∂ν := by
  obtain ⟨B, hB, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form ν Θ hm hb
  have hr : ∀ v : Θ, ∃ r : ℝ, 0 ≤ r ∧ B v v = r := fun v =>
    ⟨∫ x, ‖(v : X → ℂ) x‖ ^ 2 ∂ν, integral_nonneg fun x => by positivity, by
      rw [hB]
      simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]⟩
  let N : Θ →ₗ[ℂ] Θ := M.restrict hM
  let B' : Θ →ₗ[ℂ] Θ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B (N u) (N v))
    (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp only [map_smul, LinearMap.map_smulₛₗ])
  have hd : ∀ v : Θ, B' v v = B v v := fun v => by
    show B (N v) (N v) = B v v
    obtain ⟨r, hr0, e⟩ := hr v
    obtain ⟨s, hs0, e'⟩ := hr (N v)
    have h1 := hn v v.2
    have h2 := hN v
    have h3 := hN (N v)
    rw [e, Complex.ofReal_re] at h2
    rw [e', Complex.ofReal_re] at h3
    have h4 : ENNReal.ofReal s = ENNReal.ofReal r := h3.symm.trans (h1.trans h2)
    rw [e, e', (ENNReal.ofReal_eq_ofReal_iff hs0 hr0).1 h4]
  have key := sesq_eq_of_diag B' B hd ⟨f, hf⟩ ⟨f', hf'⟩
  exact (hB (N ⟨f, hf⟩) (N ⟨f', hf'⟩)).symm.trans (key.trans (hB ⟨f, hf⟩ ⟨f', hf'⟩))

theorem scalar_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 M hM hn f f' hf hf'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f}
      add_mem' := GlobalTheory.WeilVacMove.isTheta_add
      zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
      smul_mem' := fun c _ h => GlobalTheory.WeilVacMove.isTheta_smul c h }
  have hb : ∀ g ∈ Θ, ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := fun g (hg : IsThetaFunO ψ S T g) => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  exact integral_mul_star_eq (μ.restrict 𝓕) Θ (fun g (hg : IsThetaFunO ψ S T g) => hg.cont.measurable) hb M hM hn
    f f' hf hf'

end GlobalTheory.Mem.LiftPolar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddiStatement
section
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) = ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * coeff (blockGraph τ) G := by
  first | exact @GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | exact GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | (intros; apply GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBotStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  first | exact @GlobalTheory.unipRad_stdBlocks_two_ne_bot | exact GlobalTheory.unipRad_stdBlocks_two_ne_bot | (intros; apply GlobalTheory.unipRad_stdBlocks_two_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationEqUniformizer
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaStep
open GlobalTheory.IwaCell GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem valuation_eq_uniformizer {ϖ : kˣ} (hϖ : ord k ϖ = 1) : valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_pos.ne' hy.symm
  let π₀ : kˣ := Units.mk0 y hy0
  have h1 : ord k π₀ = 1 := ord_eq_one (by simpa [π₀] using hy)
  have h2 : ord k (ϖ * π₀⁻¹) = 0 := by
    rw [ord_mul, show π₀⁻¹ = π₀ ^ (-1 : ℤ) by simp, ord_zpow, h1, hϖ]; ring
  have h3 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at h3
  have hne : valuation k (π₀ : k) ≠ 0 := by simp
  rw [mul_inv_eq_one₀ hne] at h3
  rw [h3]
  simpa [π₀] using hy

theorem diagT_neg (ϖ : kˣ) (d : Fin m → ℤ) : diagT k (Fin m) (fun i => ϖ ^ (-d i)) = (tD ϖ d)⁻¹ := by
  rw [← tD_neg]
  rfl

theorem contracts_neg {ϖ : kˣ} (hϖ : ord k ϖ = 1) {d : Fin m → ℤ} (hd : Monotone d) :
    Contracts (fun i => ϖ ^ (-d i)) :=
  GlobalTheory.IwahoriTraceProof.dominantContracts ϖ (valuation_eq_uniformizer hϖ) (fun i => -d i)
    fun _ _ h => neg_le_neg (hd h)

theorem conj_mem_unipLowerOne {ϖ : kˣ} (hϖ : ord k ϖ = 1) {d : Fin m → ℤ} (hd : Monotone d) {u : GL (Fin m) k}
    (hu : u ∈ unipLowerOne k (Fin m)) : tD ϖ d * u * (tD ϖ d)⁻¹ ∈ unipLowerOne k (Fin m) := by
  have := (contracts_neg hϖ hd).2 u hu
  rwa [diagT_neg, inv_inv] at this

end GlobalTheory.IwaStep
end
end

