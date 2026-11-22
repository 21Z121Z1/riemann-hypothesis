import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelLocalOperatorAction
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThK.LocalOps
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
theorem theta_kernel_local_operators_act (_hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  have hex : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ :=
    fun x hx1 hx2 φ hφ => acts_exists hP v x hx1 hx2 φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun u hu φ hφ => ?_, GlobalTheory.T.weilRep_smooth_at_finitePlace B X W M χX χW om r s r' s' hP v hex⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex (g, h) hg hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 h2⟩
  · refine ⟨GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ,
      ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hP.base.std.1 v _ φ hφ, GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ⟩,
      fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)⟩
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_local_operator_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ActsEx := by
  first | exact @_root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | exact _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | (intros; apply _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsDenseInCuspForms
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaApproxX
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ F hF v hint C hC ε hε
  have hw := (hG.arrows.X i j hi hj).weil
  have hθ : IsInfFam R.θ := hRB.inf
  have hψ : IsStdChar D R.ψ (-1) := hw.std
  let AF := GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.V (i + 1) j).M)
  let BF := GlobalTheory.ChainFr.Fr.ofModel (G.V i j).M
  have hcart : ∀ τ, AF.cart τ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) τ := fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  have hpt : ∀ f P, GlobalTheory.ChainFr.ptF R.ψ R.θ AF BF f P = GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f P := by
    intro f P
    unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
    rw [show AF.cart = GlobalTheory.Grid.cartS true (G.V (i + 1) j) from funext hcart]
    rfl
  have hfin : ∀ f, GlobalTheory.ChainFr.IsVacF R.ψ R.θ AF BF f → GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f := by
    intro f hf
    refine ⟨hf.1, fun τ => ?_⟩
    have := hf.2 τ
    rwa [hcart τ] at this
  have hk : ∀ h g f, thetaKO (G.X i j).ω h g f =
      thetaKO ((G.X i j).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g f := by
    intro h g f
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  obtain ⟨μW, 𝓕W, hμW⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) (V := GlobalTheory.Grid.neg (G.V (i + 1) j).V) (W := (G.V i j).V)
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _ AF BF R.θ R.ψ hψ hθ μW 𝓕W hμW Φ hΦ
  obtain ⟨Aexp, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.V (i + 1) j).V).rank (G.V i j).V.rank
  obtain ⟨Ck, hCk0, hCk⟩ := (H _ _ rfl rfl).real R.ψ hθ hU
  have hFr := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ (G.V i j).M R.θ hθ ∅ 1 F hF v
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  obtain ⟨Hh, hHh⟩ := hC.bddAbove_image
    ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V)).continuousOn
  set Hq : ℝ := max Hh 1 with hHq
  have hHC : ∀ h ∈ C, GlobalTheory.Grow.height _ ((GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h) ≤ Hq :=
    fun h hh => (hHh ⟨h, hh, rfl⟩).trans (le_max_left _ _)
  have hq1 : (1 : ℝ) ≤ Hq := le_max_right _ _
  have hqm : AEStronglyMeasurable (fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ))
      ((G.meas t i j).ν.restrict (G.meas t i j).fd) :=
    (Complex.continuous_ofReal.comp ((GlobalTheory.Grow.continuous_quotHeight _).pow Aexp)).aestronglyMeasurable
  have hQ : IntegrableOn ((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v)
      (G.meas t i j).fd (G.meas t i j).ν :=
    hFr.2.2.integrableOn_mul_of_le hM.1 hM.2 hqm (C := 1) (A := Aexp) fun g => by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _), one_mul]
  set K0 : ℝ := ∫ g in (G.meas t i j).fd,
    ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν with hK0def
  have hK0 : 0 ≤ K0 := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := Ck * 2 ^ Aexp * Hq ^ Aexp * K0 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set δ : ℝ := ε / (M + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨g0, hg0, hg0U, hsob⟩ := hdense d (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hsum⟩ := Submodule.mem_span_set'.1 hg0
  choose f₀ P hvac hlev heq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hfin _ (hvac l), fun h hh => ?_⟩
  have hg0eq : g0 = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [heq l, hpt, map_smul]
  have hCA := (hL D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  have hintl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g)
      (G.meas t i j).fd (G.meas t i j).ν := fun l => by
    obtain ⟨F', -, hF'⟩ := hCA (f₀ l) (hfin _ (hvac l)) F hF
    exact (hF' (c l • P l) v h).1
  have hdiff : (∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) -
      ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g ∂(G.meas t i j).ν =
      ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν := by
    rw [← integral_finset_sum _ (fun l _ => hintl l),
      ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hintl l)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [thetaKO, hg0eq, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [hdiff]
  have hΞ : Φ - g0 ∈ GlobalTheory.Size.thetaLevel R.ψ _ _ U := sub_mem hΦU hg0U
  obtain ⟨hsT, hbd⟩ := hCk _ _ _ hw μW 𝓕W hμW (Φ - g0) hΞ
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μW 𝓕W d (Φ - g0)).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs : s ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal hδ.le] at this
  set h' := (GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h with hh'
  have hpt' : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
      Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp := by
    intro g
    have hinv : ∀ γ ∈ GQ (G.V i j).V, ∀ g, thetaKO (G.X i j).ω h (γ * g) (Φ - g0) = thetaKO (G.X i j).ω h g (Φ - g0) := by
      intro γ hγ g
      rw [hk, hk]
      exact GlobalTheory.Chain.LiftConv.thetaKO_left hw hΞ.1 h' γ hγ g
    have hb : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
        (Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp) * GlobalTheory.Grow.height _ g ^ Aexp := by
      intro g
      have := hbd h' g
      rw [mul_pow, ← mul_assoc] at this
      rw [hk]
      exact this
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow hinv hb g).trans ?_
    have h1 : GlobalTheory.Grow.height _ h' ^ Aexp ≤ Hq ^ Aexp :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ h').le (hHC h hh) _
    have h2 : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _
    have h3 : 0 ≤ Ck * s := mul_nonneg hCk0 hs0
    have h4 : Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp ≤ Ck * s * Hq ^ Aexp := mul_le_mul_of_nonneg_left h1 h3
    have h5 : (0 : ℝ) ≤ 2 ^ Aexp := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h4 (mul_nonneg h5 h2)]
  calc ‖∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν‖
      ≤ ∫ g in (G.meas t i j).fd, (Ck * s * Hq ^ Aexp * 2 ^ Aexp) *
          ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν := by
        refine norm_integral_le_of_norm_le (hQ.norm.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul, Pi.mul_apply, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)]
        calc ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ * ‖F v g‖
            ≤ (Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp) * ‖F v g‖ :=
              mul_le_mul_of_nonneg_right (hpt' g) (norm_nonneg _)
          _ = _ := by ring
    _ = (Ck * s * Hq ^ Aexp * 2 ^ Aexp) * K0 := integral_const_mul _ _
    _ ≤ (Ck * δ * Hq ^ Aexp * 2 ^ Aexp) * K0 := by gcongr
    _ = δ * M := by rw [hMdef]; ring
    _ < ε := by
        rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
end GlobalTheory.ThetaApproxX
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lifts_dense_in_cusp_forms : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.ThetaApproxX.upperArrow_approx | exact _root_.GlobalTheory.ThetaApproxX.upperArrow_approx | (intros; apply _root_.GlobalTheory.ThetaApproxX.upperArrow_approx <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsSeparateOfSeparatingData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section
namespace GlobalTheory.SepRows.SepProof
section
open Classical
end
set_option maxHeartbeats 1000000 in
open Classical in
theorem theta_lifts_separate_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  intro _
  unfold TopSep All
  intro D _ T L μ0 _ sc G W M hM S MB F' hF' Ψ hΨ
  have hθ : IsInfFam W.θ := W.θ_is
  set T' : MMap MB := PiTensorProduct.lift.symm F' with hT'
  have hT'm : T' ∈ Mult W.θ MB ∅ 1 := (mem_multT W.θ MB ∅ 1 F').1 hF'
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits W M hM
  have hφ : ∀ ξ, pairVec (coefPlus G W.θ) ξ Ψ ∈ contLeft (G.V (.top 0)) := fun ξ =>
    ⟨GlobalTheory.RowBplus.pairVec_cont G W.θ hθ ξ hΨ, fun γ hγ g => GlobalTheory.RowBplus.pairVec_left G W.θ ξ hΨ hγ g⟩
  have H := fun ξ => GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact W M hM Ω hΩc hΩ _ (hφ ξ)
  choose C hC using H
  have hadd := fun ξ => (hC ξ).1
  have hadd' := fun ξ => (hC ξ).2.1
  have hbd := fun ξ => (hC ξ).2.2
  have hTt : ∀ u : MB.Vec, F' (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : F' = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply F').symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT MB, F' x ∈ contLeft (G.V (.grid D.R.m 0)) := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft _).smul_mem r (GlobalTheory.Core.Mi.SepPer.mult_mem_contLeft W.θ MB ∅ 1 hT'm u)
    | add x y hx hy =>
      rw [map_add]
      exact (contLeft _).add_mem hx hy
  have pv_add : ∀ ξ ξ', pairVec (coefPlus G W.θ) (ξ + ξ') Ψ = pairVec (coefPlus G W.θ) ξ Ψ + pairVec (coefPlus G W.θ) ξ' Ψ := by
    intro ξ ξ'; funext h; simp [pairVec_apply]
  have pv_smul : ∀ (a : ℂ) ξ, pairVec (coefPlus G W.θ) (a • ξ) Ψ = a • pairVec (coefPlus G W.θ) ξ Ψ := by
    intro a ξ; funext h; simp [pairVec_apply]
  have hBadd : ∀ ξ ξ' F, F ∈ contLeft (G.V (.grid D.R.m 0)) → Bplus W M (pairVec (coefPlus G W.θ) (ξ + ξ') Ψ) F =
      Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F + Bplus W M (pairVec (coefPlus G W.θ) ξ' Ψ) F := by
    intro ξ ξ' F hF; rw [pv_add]; exact hadd' ξ _ (hφ ξ') F hF
  have hBsmul : ∀ (a : ℂ) ξ F, Bplus W M (pairVec (coefPlus G W.θ) (a • ξ) Ψ) F = a * Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F := by
    intro a ξ F
    rw [pv_smul]; exact Bplus_smul_left W M a _ F
  have hBsmulR : ∀ (a : ℂ) φ F, Bplus W M φ (a • F) = a * Bplus W M φ F := by
    intro a φ F
    exact Bplus_smul_right W M a φ F
  refine ⟨⟨LinearMap.mk₂ ℂ (fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v))
      (fun ξ ξ' v => hBadd ξ ξ' _ (hmem v)) (fun a ξ v => hBsmul a ξ _)
      (fun ξ v v' => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_add v v')).trans (hadd ξ _ (hmem v) _ (hmem v')))
      (fun a ξ v => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_smul a v)).trans (hBsmulR a _ _)), fun ξ v => rfl⟩, ?_⟩
  intro Wt _ _ π e he τ x v
  have hE : ∀ (y y' : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (y + y'))) =
      e (PiTensorProduct.tprod ℂ (Function.update x τ y)) + e (PiTensorProduct.tprod ℂ (Function.update x τ y')) := by
    intro y y'; rw [MultilinearMap.map_update_add, map_add]
  have hEs : ∀ (a : ℂ) (y : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (a • y))) =
      a • e (PiTensorProduct.tprod ℂ (Function.update x τ y)) := by
    intro a y; rw [MultilinearMap.map_update_smul, map_smul]
  have hV : ∀ (u u' : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (u + u'))) =
      F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) + F' (PiTensorProduct.tprod ℂ (Function.update v τ u')) := by
    intro u u'; rw [MultilinearMap.map_update_add, map_add]
  have hVs : ∀ (a : ℂ) (u : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (a • u))) =
      a • F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) := by
    intro a u; rw [MultilinearMap.map_update_smul, map_smul]
  have hF1 : ∀ (g : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.grid D.R.m 0)).rank) ℂ),
      g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.grid D.R.m 0)) τ) → ∀ (x₁ y₁ : MB.sm τ), (y₁ : MB.H τ) = MB.rep τ g x₁ →
      F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁)) =
        rTr _ (atTau W.θ _ τ g) (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁))) := by
    intro g hg x₁ y₁ hy
    rw [hTt, hTt]
    have := mult_equiv W.θ MB ∅ 1 hT'm τ hg (Function.update v τ x₁) y₁ (by simpa using hy)
    simpa using this
  obtain ⟨Lw, Cu, hL, hb⟩ := GlobalTheory.Core.Mi.SepPer.mult_bound (θ := W.θ) hθ MB (∅ : Set (GA D (G.V (.grid D.R.m 0)))) 1 hT'm Ω hΩc τ v
  refine ⟨LinearMap.mk₂ ℂ (fun y u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))))
      (fun y y' u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hE y y')).trans (hBadd _ _ _ (hmem _)))
      (fun a y u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hEs a y)).trans (hBsmul _ _ _))
      (fun y u u' => (congrArg (Bplus W M _) (hV u u')).trans (hadd _ _ (hmem _) _ (hmem _)))
      (fun a y u => (congrArg (Bplus W M _) (hVs a u)).trans (hBsmulR _ _ _)), ⟨?_, ?_, ?_⟩, fun y u => rfl⟩
  · intro y
    have hℓ0 := fun (u u' : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hV u u')).trans
        (hadd _ _ (hmem _) _ (hmem _))
    have hℓ1 := fun (a : ℂ) (u : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hVs a u)).trans
        (hBsmulR a _ _)
    let ℓ₀ : MB.sm τ →ₗ[ℂ] ℂ :=
      { toFun := fun u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
          (F' (PiTensorProduct.tprod ℂ (Function.update v τ u)))
        map_add' := hℓ0
        map_smul' := hℓ1 }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ u : MB.sm τ, ℓ u = Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
        (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))) := fun u => congrArg (fun m => m u) hℓ
    refine ⟨ℓ, ⟨Lw, C (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) * Cu, hL, fun w hw => ?_⟩, fun u => hℓw u⟩
    have hw' : w ∈ MB.sm τ := Submodule.subset_span hw
    have e1 : ℓ w = ℓ ((⟨w, hw'⟩ : MB.sm τ) : MB.H τ) := rfl
    rw [e1, hℓw]
    have := hbd (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) _ (hmem _) _
      (fun z hz => by rw [hTt]; exact hb ⟨w, hw'⟩ z hz)
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro h hh g hg hEm w x₁ y₁ hy
    have he1 := he τ h hh (Function.update x τ w) (Function.update x τ (π τ h w)) (by simp) (fun τ' hτ' => by simp [hτ'])
    have hp := pairVec_comp_rho (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ
      (atTau_mem_GinfC' W.θ _ τ h)
    have hemb : atTau W.θ (G.V (.grid D.R.m 0)) τ g = embTop G (atTau W.θ (G.V (.top 0)) τ h) :=
      (embRel_iff _ _ _).1 (GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding D W.θ hθ _ _ _ τ h g hh hg hEm)
    show Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ (π τ h w)))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) =
      Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [he1, hp, hF1 g hg x₁ y₁ hy, hemb]
    exact GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate W M hM _ (hφ _) _ (hmem _) _
  · intro u hu w x₁ y₁ hy
    show Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) = _ * Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [hF1 u hu.1 x₁ y₁ hy]
    exact GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent W M hM _ _ (hmem _) _ (GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic D W.θ hθ _ G.besTop.e τ u hu)
end GlobalTheory.SepRows.SepProof
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lifts_separate_points : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  first | exact @_root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | exact _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLineDerivVanishesOnCoinvariants
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.OmegaDer
section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Mat
variable {D : D7}
theorem line_deriv_theta_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω he Xs hJ f₀ hf γ hγ
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_line M hc Xs hJ γ hγ
  refine ⟨g, h1, fun P => ?_⟩
  obtain ⟨Z, hZ, hd⟩ := der_line (V := sgn ε M) (ω := ω.toSgn ε) hθ hω (frSgn ε A) B he hf
    (fun t => (ofSgn ε M).symm (g t)) ((continuous_ofSgn_symm ε M).comp h2)
    (fun s t => by rw [h3, map_mul]) h4
  refine ⟨_, ?_, hd P⟩
  refine Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, Z τ, ?_, P, ?_⟩
  · rw [← GlobalTheory.SgnIdent.lieAt_sgn ε M τ]
    exact hZ τ
  · rw [neg_smul, ← sub_eq_add_neg]
    rfl
end GlobalTheory.OmegaDer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lineDeriv_vanishes_on_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  first | exact @_root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | exact _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | (intros; apply _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairModerateGrowth
section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.ThetaModGrowthPair
theorem theta_moderate_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale
  have hfin := GlobalTheory.T.weilRep_rational_support_common_denominator
  have harch := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring
end GlobalTheory.ThetaModGrowthPair
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_moderate_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @_root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth | exact _root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth | (intros; apply _root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumOmegaRational
section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace GlobalTheory.ThetaRatPair
theorem theta_sum_omega_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end GlobalTheory.ThetaRatPair
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_sum_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @_root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | exact _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | (intros; apply _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational <;> assumption)
end
end

