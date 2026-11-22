import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOneOfSerOf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapPhaseOne

set_option maxHeartbeats 1000000 in

theorem phRat_of_serOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsGrp F → R.IsThP → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hG hP' t O i hpins cc hser hex hequiv
  obtain ⟨hcc, hph, hs⟩ := hser
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  refine GlobalTheory.PhaseRationalDegenerate.of_before_projector (O i) (κ i) _ cc hequiv hG.chiW hP'.thG 1 fun x₀ => ?_
  obtain ⟨h, J', hrep, hP, -, -⟩ := (hpins.2.tuple ()).reps
  obtain ⟨x, hx⟩ := hP x₀
  obtain ⟨f, hf, hcl⟩ := hex x
  have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
    rw [hn]; exact hf
  have hBC := GlobalTheory.PhRatCommon.exists_rdU_eq_sum (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') _ _ f hf'
  obtain ⟨m, as, fs, hbc⟩ := hBC
  have hL : ∀ a : (O i).c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' a := fun a => by
    have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ a.2
    exact this
  choose b hb using hL
  refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
  have := hs () h J' hrep _ x hx f hf.1 hcl g
  have e1 := hbc ((O i).dict g).1 ((O i).dict g).2
  have e2 : ∀ j, (O i).phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc ((O i).dict g).1 * (O i).mu g *
      rdU (T.U ((i : ℕ) + 1) (O i).s0) (fs j : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := fun j => rfl
  exact this.trans (GlobalTheory.PhRatCommon.sum_shape e1 (fun j => hb (as j)) e2)

set_option maxHeartbeats 1000000 in

theorem oneMapOf_one_of_serOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsGrp F → R.IsThP → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hG hP' t O i hpins cc hS hE hequiv
  refine ⟨hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, ?_⟩,
    phRat_of_serOf D G Pl0 T0 A T R F κ v₀ hG hP' t O i hpins cc hS hE hequiv⟩
  refine ⟨hS.1, hS.2.1, 1, Subgroup.one_mem _, fun t => ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx => ⟨hE x, ?_⟩⟩⟩
  intro f hf hT q
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hpins.2.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hpins.2.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) (O i).c' (O i).lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := hS.2.2 t h J' hR _ x hx₀ f hf hT q.out
  rw [h1, hA _ x hx₀, one_mul (cc _)]
  refine h2.trans ?_
  rw [mul_assoc (cc _ * _)]
  rfl

theorem exists_oneMapOf_one : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∃ cc, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio O i hpins
  obtain ⟨cc, -, u, -, hequiv, hser, -⟩ :=
    GlobalTheory.T.oscillator_model_extension_third hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i _ _ (O i) hpins.2
  exact ⟨u • cc, oneMapOf_one_of_serOf D G Pl0 T0 A T R F κ v₀ hR.grp hR.thP ht O i hpins (u • cc) hser
    (GlobalTheory.T.oscillator_model_values_sixth hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ (O i) hpins.2 ()) hequiv⟩

end GlobalTheory.OneMapPhaseOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatementStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.page_estimate_statement : PageSt := by
  first | exact @GlobalTheory.BigOn.pageSt | exact GlobalTheory.BigOn.pageSt | (intros; apply GlobalTheory.BigOn.pageSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlockEigenRelationStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_frame_block_eigen_relation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J), (∀ i, 0 < t i) → IsTorusU x y t a →
      ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
        ‖e (om (a * κ, h) (pureA F f φ)) z‖ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := by
  first | exact @GlobalTheory.ThKTorus.Scale.norm_eval_torus_le | exact GlobalTheory.ThKTorus.Scale.norm_eval_torus_le | (intros; apply GlobalTheory.ThKTorus.Scale.norm_eval_torus_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open MeasureTheory

namespace GlobalTheory.HSApp.NormProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)
  {D : D7} (V : TH.HSp D) (dict : Formalism.L2.Theta.GA D V → (k : U.Comp) × FD.Frame (U.X k).Ψ r) (μ : Measure (AutQ V))

theorem ptN_rdU_le {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c} (hf : rdU U f ∈ holSub U.X la)
    (z : (k : U.Comp) × FD.Frame (U.X k).Ψ r) : AllWt.ptN la (rdU U f) z ≤ (supE U.X la (rdU U f)).toReal := by
  by_cases h : z.2 ∈ (U.X z.1).dom
  · have h1 : ENNReal.ofReal (AllWt.ptN la (rdU U f) z) ≤ supE U.X la (rdU U f) :=
      le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2)) ⟨z.1, ⟨z.2, h⟩⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top U.X la hf)).1 h1
  · have h0 : AllWt.ptN la (rdU U f) z = 0 := by
      simp [AllWt.ptN, FD.Data.pnorm, rdU, h]
    rw [h0]; exact ENNReal.toReal_nonneg

theorem petE_rdU_ne_top (hμ : μ Set.univ ≤ 1) {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X la) : AllWt.petE V dict μ la (rdU U f) ≠ ⊤ := by
  have hb : ∀ᵐ q ∂μ, ‖AllWt.ptN la (rdU U f) (dict (Quotient.out q))‖ ≤ (supE U.X la (rdU U f)).toReal :=
    Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _)]; exact ptN_rdU_le U hf _
  refine ne_top_of_le_ne_top ?_ (eLpNorm_le_of_ae_bound hb)
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ)

theorem eLpNorm_homN_ne_top (hμ : μ Set.univ ≤ 1) {G : WTZ E} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    eLpNorm (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) 2 μ ≠ ⊤ := by
  have : (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) =
      AllWt.lieFacZ Dw x G • fun q : AutQ V => AllWt.ptN (AllWt.modelWt U G) (rdU U f) (dict (Quotient.out q)) := rfl
  rw [this, eLpNorm_const_smul]
  exact ENNReal.mul_ne_top enorm_ne_top (petE_rdU_ne_top U V dict μ hμ hf)

theorem homN_le_of_berg (hμ : μ Set.univ ≤ 1) (y : FPt U.X) {B : ℝ} (hB0 : 0 ≤ B) {G : WTZ E}
    (hB : AllWt.bergE V dict μ (AllWt.modelWt U G) y ≤ ENNReal.ofReal B) {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    AllWt.homN U x G f ⟨y.1, y.2.1⟩ ≤ Real.sqrt B * AllWt.petAt U x V dict μ G f := by
  have hfin := petE_rdU_ne_top U V dict μ hμ hf
  have h1 : ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) (rdU U f) ⟨y.1, y.2.1⟩) ^ 2 /
      AllWt.petE V dict μ (AllWt.modelWt U G) (rdU U f) ^ 2 ≤ ENNReal.ofReal B :=
    (le_iSup₂ (f := fun P (_ : P ∈ holSub U.X (AllWt.modelWt U G)) =>
      ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) P ⟨y.1, y.2.1⟩) ^ 2 /
        AllWt.petE V dict μ (AllWt.modelWt U G) P ^ 2) (rdU U f) hf).trans hB
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top hfin))] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) h1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB0, ENNReal.toReal_pow] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (AllWt.lieFacZ Dw x G))
  have h4 : AllWt.homN U x G f ⟨y.1, y.2.1⟩ ^ 2 ≤ B * AllWt.petAt U x V dict μ G f ^ 2 := by
    unfold AllWt.homN AllWt.petAt
    nlinarith [h3]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (AllWt.homN_nonneg _ _ _ _ _), Real.sqrt_mul hB0, Real.sqrt_sq (AllWt.petAt_nonneg _ _ _ _ _ _ _)] at h5

end GlobalTheory.HSApp.NormProd

namespace GlobalTheory.HSApp

open MeasureTheory in

theorem petOn_mul_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  intro D T j Y e o _ _ Z a b w f β hβ hB σ
  set σ' := goodOf Y.d.c₂ σ with hσ'
  have hg : GoodEmb Y.d.c₂ σ' := Formalism.L2.PjFree.goodEmb_goodOf Y.d.c₂ σ
  set μ := AllWt.muOn (Y.U σ') (D.sp.W j) (Y.dict σ') Z with hμdef
  have hμ : μ Set.univ ≤ 1 := AllWt.muPart_univ_le _ _ _
  have hwH := (AllWt.mem_cuspW.1 w.2.1).2 σ' hg
  have hfH := (AllWt.mem_cuspW.1 f.2.1).2 σ' hg
  have hab : AllWt.wtOf (T.Q.Dw j) (a + b) 0 = AllWt.wtOf (T.Q.Dw j) a 0 + AllWt.wtOf (T.Q.Dw j) b 0 :=
    AllWt.wtOf_add a b 0 0
  set Pa := AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) a 0) w.1 with hPa
  have hPa0 : 0 ≤ Pa := AllWt.petAt_nonneg _ _ _ _ _ _ _
  have hpt : ∀ z : (k : (Y.U σ').Comp) × FD.Frame ((Y.U σ').X k).Ψ D.R.r,
      AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z ≤
        (Real.sqrt β * Pa) * AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) f.1 z := by
    intro z
    by_cases hz : z ∈ AllWt.framesOn (Y.U σ') Z
    · obtain ⟨h, -⟩ := id hz
      rw [hab, AllWt.homN_mul _ _ (AllWt.even_wtOf _ _) (AllWt.even_wtOf _ _) _ _ z h]
      refine mul_le_mul_of_nonneg_right ?_ (AllWt.homN_nonneg _ _ _ _ _)
      have hy := hB σ' hg ⟨z.1, ⟨z.2, h⟩⟩ hz
      exact NormProd.homN_le_of_berg (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ ⟨z.1, ⟨z.2, h⟩⟩ hβ hy hwH
    · have h0 : rdU (Y.U σ') w.1 z.1 z.2 = 0 := AllWt.rdU_eq_zero (Y.U σ') w.2.2 hz
      have h1 : AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z = 0 := by
        simp only [AllWt.homN, AllWt.ptN, FD.Data.pnorm, AllWt.rdU_mul, Pi.mul_apply, h0, zero_mul, norm_zero, mul_zero]
      rw [h1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0) (AllWt.homN_nonneg _ _ _ _ _)
  have key : eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0)
      (w.1 * f.1) (Y.dict σ' (Quotient.out q))) 2 μ ≤
      ENNReal.ofReal (Real.sqrt β * Pa) * eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ := by
    rw [← Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0), ← eLpNorm_const_smul]
    refine eLpNorm_mono_real fun q => ?_
    rw [Real.norm_of_nonneg (AllWt.homN_nonneg _ _ _ _ _)]
    exact hpt _
  have hfin := NormProd.eLpNorm_homN_ne_top (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ hfH
  have k2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0)] at k2
  show AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ (w.1 * f.1) ≤
    Real.sqrt β * Pa * AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ f.1
  rw [AllWt.petAt_eq, AllWt.petAt_eq (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) b 0)]
  exact k2

end GlobalTheory.HSApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMul
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.PetTw

theorem homN_mul_sig_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ suppOn Z)
    (σ : c.F →+* ℂ) (z : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = s.cInf σ * homN (U (goodOf c σ)) x G f z := by
  by_cases hz : z ∈ framesOn (U (goodOf c σ)) Z
  · rw [s.homN_mul_sig hG f hz, mul_comm]
  · have h1 : rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2 = 0 :=
      rdU_eq_zero _ (mul_mem_suppOn f s.sig_mem_suppOn) hz
    have h2 : rdU (U (goodOf c σ)) f z.1 z.2 = 0 := rdU_eq_zero _ hf hz
    show _ * (‖rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2‖ * _) = s.cInf σ * (_ * (‖rdU (U (goodOf c σ)) f z.1 z.2‖ * _))
    rw [h1, h2, norm_zero, zero_mul, zero_mul, mul_zero, mul_zero, mul_zero]

theorem petAt_mul_sig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG f hf σ D V dict μ
  rw [petAt_eq, petAt_eq]
  have e : (fun q : AutQ V => homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) (dict q.out)) =
      s.cInf σ • fun q : AutQ V => homN (U (goodOf c σ)) x G f (dict q.out) :=
    funext fun q => homN_mul_sig_eq s hG hf σ (dict q.out)
  rw [e, eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal (s.cInf_pos σ).le,
    ENNReal.toReal_ofReal (s.cInf_pos σ).le]

end GlobalTheory.FlatTw.PetTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointFactorIntegralSubalgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i → (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T), t ≫ p = spMap (algebraMap K B) → ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u := by
  first | exact @GlobalTheory.point_factor_integral_subalgebra | exact GlobalTheory.point_factor_integral_subalgebra | (intros; apply GlobalTheory.point_factor_integral_subalgebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixExp

theorem pow_mul_le_of_cls_eq {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)]
    (h : Published.NefProductNonneg) (hp : IsProjOver (strHom k Y)) {e : ℕ}
    (hD : topologicalKrullDim Y = e) {N N' N₀ : LB Y} (hN : IsNef k N) (hN' : IsNef k N')
    (h₀ : N₀.IsLB) (a b : ℕ) (hc : cls N₀ h₀ = a • cls N hN.isLB + b • cls N' hN'.isLB) :
    (a : ℤ) ^ e * interNum k (structureModule Y) (fun _ : Fin e => N) ≤
      interNum k (structureModule Y) (fun _ : Fin e => N₀) := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k Y) (structureModule Y) hp
    (d := e) (by rw [suppDim_structureModule, hD])
  have hL : ∀ j, IsNef k ((![N, N'] : Fin 2 → LB Y) j) := fun j => by
    fin_cases j
    exacts [hN, hN']
  have e₁ := H.interNum_of_cls_eq_sum (L := ![N, N']) (fun j => (hL j).isLB)
    (Q := fun _ => N₀) (fun _ => h₀) (fun _ => ![(a : ℤ), (b : ℤ)])
    (fun _ => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natCast_zsmul]
      exact hc)
  have e₂ := Finset.single_le_sum
    (f := fun c : Fin e → Fin 2 =>
      (∏ i, (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) (c i)) *
        interNum k (structureModule Y) (![N, N'] ∘ c))
    (fun c _ => mul_nonneg (Finset.prod_nonneg fun i _ => by
        generalize c i = j
        fin_cases j <;> simp)
      (h.interNum_nonneg (N := ![N, N'] ∘ c) hp hD fun i => hL (c i)))
    (Finset.mem_univ fun _ => 0)
  rw [e₁]
  refine le_trans (le_of_eq ?_) e₂
  simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.MixExp

open GlobalTheory.MixExp in

theorem GlobalTheory.mixExp_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  intro h k _ X q hq
  letI := algebraΓOfHom q
  intro N N' N₀ hN hN' h₀ a b Z e hnef hnef' hc hZ
  have hp : IsProjOver (strHom k X) := by rwa [strHom_eq (f := q) fun _ => rfl]
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  change (a : ℤ) ^ e * interNumOn k (redι Z) (fun _ : Fin e => N) ≤
    interNumOn k (redι Z) (fun _ : Fin e => N₀)
  rw [interNumOn_eq_interNum_pull hi fun _ => hN, interNumOn_eq_interNum_pull hi fun _ => h₀]
  refine pow_mul_le_of_cls_eq h.1 hpZ ((topologicalKrullDim_red Z).trans hZ)
    (hnef.pull_of_isClosedImmersion (redι Z) hi) (hnef'.pull_of_isClosedImmersion (redι Z) hi)
    (LB.isLB_pull h₀ (redι Z)) a b ?_
  rw [cls_pull h₀, cls_pull hN, cls_pull hN', hc, map_add, map_nsmul, map_nsmul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullBig

open GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 Filter

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (σ : X ⟶ Y)
    (hσ : DenseRange σ) : σ (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image σ.continuous
  rw [Set.image_univ, hσ.closure_range] at h
  exact h.eq (genericPoint_spec Y)

theorem pull_top_injective {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : Y ⟶ Sp k} (σ : X ⟶ Y) (hσ : DenseRange σ) (B : LB Y) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top) := by
  have hη := map_genericPoint σ hσ
  have hF : IsField (Y.presheaf.stalk (σ (genericPoint X))) := by
    rw [hη]; exact Field.toIsField Y.functionField
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have hηi : genericPoint Y ∈ B.U i :=
    ((genericPoint_spec Y).mem_open_set_iff (B.U i).isOpen).2 ⟨y, Set.mem_univ _, hy.2⟩
  have hxi : σ (genericPoint X) ∈ B.U i := hη ▸ hηi
  have h0 : germ (p := p) (O := ⊤) i (σ (genericPoint X)) trivial hxi f = 0 := by
    have e := congrArg (germ (p := σ ≫ p) (B := B.pull σ) (O := ⊤) (fun _ => i) (genericPoint X) trivial (mem_pull.2 hxi)) hf
    have e' := (germ_pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top (fun _ => i) (genericPoint X) trivial
      (mem_pull.2 hxi) f).symm.trans (e.trans (map_zero _))
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    have := congrArg (σ.stalkMap (genericPoint X)).hom hb
    rw [map_mul, e', zero_mul, map_one] at this
    exact zero_ne_one this
  have hloc : f.loc i = 0 :=
    germ_injective_of_isIntegral Y (U := ⊤ ⊓ B.U i) (σ (genericPoint X)) ⟨trivial, hxi⟩
      (h0.trans (map_zero _).symm)
  exact congrArg _ hloc

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y), IsProjOver p → IsProjOver (σ ≫ p) →
    topologicalKrullDim X = topologicalKrullDim Y → DenseRange σ → ∀ L : LB Y,
    (letI := algebraΓOfHom p; IsBig k L) → (letI := algebraΓOfHom (σ ≫ p); IsBig k (L.pull σ)) := by
  intro k _ X Y _ _ p σ hp hq hdim hσ L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (σ ≫ p)
  obtain ⟨D, hD, c, hc, hm⟩ := hL.growth
  have hL' := LB.isLB_pull hL.isLB σ
  have key (m : ℕ) : lbH0 k (lbPow L m) ≤ lbH0 k (lbPow (L.pull σ) m) := by
    have hLm := isLB_lbPow hL.isLB m
    have hP := LB.isLB_pull hLm σ
    haveI := finite_top hq hP
    calc lbH0 k (lbPow L m) = Module.finrank k (H0 p (lbPow L m) ⊤) := (H0.finrank_top p _).symm
      _ ≤ Module.finrank k (H0 (σ ≫ p) ((lbPow L m).pull σ) ⊤) :=
        LinearMap.finrank_le_finrank_of_injective (pull_top_injective σ hσ _)
      _ = lbH0 k ((lbPow L m).pull σ) := H0.finrank_top _ _
      _ = lbH0 k (lbPow (L.pull σ) m) := lineBundleGlobalSectionsDim_congr_picardClass hP (isLB_lbPow hL' m) (by
        rw [cls_pull hLm, cls_lbPow hL.isLB, cls_lbPow hL', cls_pull hL.isLB, map_nsmul])
  refine (isBig_iff (fun _ => rfl) hq (hdim.trans hD)).2 ⟨hL', c, hc, hm.mono fun m hm' => ?_⟩
  exact hm'.trans (by exact_mod_cast key m)

end GlobalTheory.PullBig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS.TorFlagEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isDedFrac_id : GlobalTheory.Models.IsDedFrac (RingHom.id c.F) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

theorem pushInvertible_of_hasTheta (Y : Model Xo c (RingHom.id c.F)) (hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L) :
    PushInvertible Y.t.G Y.t.PP.L :=
  GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H Dw l _ _ _ _ _ _ Y.oF _
    (RingHom.id c.F)
    ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩ isDedFrac_id hθ

theorem one_le_of_dimFlag (h : 1 ≤ dimFlag Dw) : 1 ≤ Dw.p + Dw.q := by
  by_contra h0
  have : Dw.p + Dw.q = 0 := by omega
  simp [dimFlag, Formalism.DegreeFormula.dimFl, this] at h

end GlobalTheory.CompHS.TorFlagEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runNumericalConditions_hold_along_family : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧ 3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  first | exact @GlobalTheory.OntoNum.pageNum_along | exact GlobalTheory.OntoNum.pageNum_along | (intros; apply GlobalTheory.OntoNum.pageNum_along <;> assumption)
end

