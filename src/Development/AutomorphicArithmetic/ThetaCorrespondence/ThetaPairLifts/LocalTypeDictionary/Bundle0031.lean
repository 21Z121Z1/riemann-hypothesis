import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0722
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0006
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0728
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0651

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumIsVacuumIntegral
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_isVacuumIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_vacuum_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | exact _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairIntRatKOfThetaLocalInputs
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open GlobalTheory.SumSize.TopInt
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → GlobalTheory.SumSize.PairInt.PairIntRatK := by
  intro hP hI hD
  obtain ⟨C1, hC1, hPL⟩ := _root_.UpperTheory.WildA.ker_wild_ramification_map
  obtain ⟨C0, hC0, hS⟩ := UpperTheory.WildA.lossOne C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  refine ⟨CF2, fun CF hCF => ?_⟩
  obtain ⟨C02, hD⟩ := hD CF hCF
  refine ⟨max C0 C02, fun ε C hC => ?_⟩
  obtain ⟨x2, hD⟩ := hD ε C (le_of_max_le_right hC)
  refine ⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch := hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have hgap : ch.sc.cGap = 1 := by
    have e : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hsc
    rw [e]
  obtain ⟨S', h, hE, hh⟩ := hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL
  obtain ⟨l1, l2, l3⟩ := UpperTheory.WildA.expLoss D S' h _ hE
  obtain ⟨-, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size
  refine ⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩
  · have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hCC : C0 ≤ C := le_of_max_le_left hC
    have h1 : C0 ≤ C * D.R.m := by nlinarith
    have h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have : (0 : ℝ) ≤ large₂.sc.b := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    unfold bOne
    linarith
  · intro t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv
    have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr
      w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
    refine inLat_mono key ?_
    have h1 := kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w)
      (hdep _ (primeUnder_prime w) (primeUnder_mem w))
    have h2 := (mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))
    have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast vw_natCast_nonneg w _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [mul_assoc]
    linarith
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ParabolicDerivativeFixesSplitVector
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitDblPar
theorem parabolic_derivative_fixes_split_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.T.doubleLine_eigenspace_decomposition_split hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := _root_.GlobalTheory.T.split_det_character_trivial hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac t htp
  have hb := _root_.GlobalTheory.T.split_det_modulus_norm_formula hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]
end GlobalTheory.SplitDblPar
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_double_parabolic_derivative_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector | exact _root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector | (intros; apply _root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolynomialMatchingInduction
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.ThK.PolMatchStep
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
section Local
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end Local
theorem polynomial_matching_on_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T v hv h hh Φ Φ' hPM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hPM
  have hT := hM.triple
  have ex := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v
  have ex' := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v
  have h1 : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have h1' : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V' (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have E1 := fun x hx => (ex.1 1 h1 h hh x hx).exists
  have E1' := fun x hx => (ex'.1 1 h1' h hh x hx).exists
  let loc : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1 x hx).choose else 0
  let loc' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1' x hx).choose else 0
  have hloc : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), loc x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h)) x (loc x) := fun x hx => by
    simp only [loc, dif_pos hx]; exact (E1 x hx).choose_spec
  have hloc' : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), loc' x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)) x (loc' x) := fun x hx => by
    simp only [loc', dif_pos hx]; exact (E1' x hx).choose_spec
  have pre : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hM.fin.onto v]; trivial
    exact hy
  have pre' : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    exact hy
  let A0 : Rf.Pi v → Rf.Pi v := fun y => Rf.p v (loc (pre y).choose)
  have K : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), A0 (Rf.p v x) = Rf.p v (loc x) := by
    intro x hx
    obtain ⟨hx0, hx0e⟩ := (pre (Rf.p v x)).choose_spec
    obtain ⟨x', hx', hx'e⟩ := pre' (Rf.p v x)
    have a1 := hM.fin.equiv v h hh _ hx0 x' hx' _ (hloc _ hx0).1 _ (hloc' x' hx').1 (hloc _ hx0).2 (hloc' x' hx').2
      (hx0e.trans hx'e.symm)
    have a2 := hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2
      hx'e.symm
    exact a1.trans a2.symm
  have K' : ∀ x' ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), A0 (Rf.p' v x') = Rf.p' v (loc' x') := by
    intro x' hx'
    obtain ⟨x, hx, hxe⟩ := pre (Rf.p' v x')
    rw [← hxe, K x hx]
    exact hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hxe
  have Klin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∀ c d : ℂ, loc (c • x + d • y) = c • loc x + d • loc y := by
    intro x hx y hy c d
    have hs : c • x + d • y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((GlobalTheory.WeilM.SB _).smul_mem c hx) ((GlobalTheory.WeilM.SB _).smul_mem d hy)
    exact acts_lin_eq v (om (1, h)) hx hy (hloc x hx).2 (hloc y hy).2 c d (hloc _ hs).2
  let A : Rf.Pi v →ₗ[ℂ] Rf.Pi v :=
    { toFun := A0
      map_add' := by
        intro y z
        obtain ⟨x, hx, rfl⟩ := pre y
        obtain ⟨w, hw, rfl⟩ := pre z
        rw [← map_add, K _ (add_mem hx hw), K x hx, K w hw, ← map_add]
        congr 1
        simpa using Klin x hx w hw 1 1
      map_smul' := by
        intro c y
        obtain ⟨x, hx, rfl⟩ := pre y
        rw [← map_smul, K _ ((GlobalTheory.WeilM.SB _).smul_mem c hx), K x hx, RingHom.id_apply, ← map_smul]
        congr 1
        simpa using Klin x hx x hx c 0 }
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ hv)
  have evc : ∀ {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y G.W) (ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, w ∉ T → ρ w = M.vac w) → M.IsGood B.ψ →
      ∀ᶠ w in Filter.cofinite, ρ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    intro n Y M ρ hρ hG
    have e0 : ∀ᶠ w in Filter.cofinite, ρ w = M.vac w :=
      Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw (hρ w hc))
    filter_upwards [e0, hG.std] with w e1 e2
    rw [e1, e2]
  let φN : Fin m → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ :=
    fun i => Function.update (φ i) v (loc (φ i v))
  let φN' : Fin m' → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun j => Function.update (φ' j) v (loc' (φ' j v))
  refine ⟨m, m', f, φN, f', φN', fun i => ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩,
    fun j => ⟨(hφ' j).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; simp only [φN, Function.update_self]; exact (hloc _ ((hφ i).2.1 w)).1
    · simp only [φN, Function.update_of_ne hw]; exact (hφ i).2.1 w
  · simp only [φN, Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w hw
  · by_cases hw : w = v
    · subst hw; simp only [φN', Function.update_self]; exact (hloc' _ ((hφ' j).2.1 w)).1
    · simp only [φN', Function.update_of_ne hw]; exact (hφ' j).2.1 w
  · simp only [φN', Function.update_of_ne (hvT w hw)]; exact (hφ' j).2.2 w hw
  · rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact pure_update v (om (1, h)) (f i) (φ i) (hφ i).2.1 (evc G.M (φ i) (hφ i).2.2 hT.geo.hM)
      (hloc _ ((hφ i).2.1 v)).2
  · rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact pure_update v (om' (1, h)) (f' j) (φ' j) (hφ' j).2.1 (evc G.M' (φ' j) (hφ' j).2.2 hT.geo.hM')
      (hloc' _ ((hφ' j).2.1 v)).2
  · have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map
      (Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A))) hsum
    simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key
    have e1 : ∀ i, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p u (φ i u))) = fun u : T => Rf.p u (φN i u) := by
      intro i; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN]; exact K _ ((hφ i).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN, Function.update_of_ne hu', LinearMap.id_apply]
    have e2 : ∀ j, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p' u (φ' j u))) = fun u : T => Rf.p' u (φN' j u) := by
      intro j; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN']; exact K' _ ((hφ' j).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN', Function.update_of_ne hu', LinearMap.id_apply]
    simp only [e1, e2] at key
    exact key
end GlobalTheory.ThK.PolMatchStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_matching_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  first | exact @_root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | exact _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | (intros; apply _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVacuumAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitVacAlg
open GlobalTheory.MovedAlg
section Comb
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}
end Comb
set_option maxHeartbeats 1000000 in
theorem split_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hLμ hX t N e P hP _ h hh hs
  classical
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) :=
    fun u v hu hv => GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 (GlobalTheory.Grid.neg A) WW u v hu hv
  have hchr := _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist hPr hInp hLμ hX
  have vac : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac X.vac := isAlgComb_self
  have detAlg : ∀ (e' : AE D) (he' : IsSplitIdem D e') (g : GA D WW),
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e' he'.1 WW g) : Circle) : ℂ) :=
    fun e' he' g => hchr e' he' _ (by
      change e' * (Formalism.L2.Theta.mt WW g).det + (1 - e') =
        e' * (e' * (Formalism.L2.Theta.mt WW g).det + (1 - e')) + (1 - e')
      rw [mul_add, ← mul_assoc, he'.1, mul_sub, mul_one, he'.1, sub_self, add_zero])
  have hecke : ∀ (e' : AE D) (he' : IsSplitIdem D e') (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW),
      Formalism.L2.NTheta.IsHeckeElt (stdLatSp WW hX.stdW.1) e' (ϖ : D.host.E) k α →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, α) X.vac) := by
    intro e' he' ϖ k α hα
    obtain ⟨Δ, hΔ, heq⟩ := GlobalTheory.T.definiteBottom_splitHecke_vacuum hX t e' he' ϖ k α hα
    rw [heq]
    exact (isAlgComb_sum Δ hΔ).smul (isAlg_mul (detAlg e' he' α) (isAlg_sqrt_inv _))
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (by
      simpa using Ideal.pow_right_strictAnti P.asIdeal P.ne_bot P.isPrime.ne_top (by norm_num : 1 < 2))
  have gen := GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure (stdLatSp WW hX.stdW.1) P e ϖ hP hϖ hϖ2 h hh hs
  refine Submonoid.closure_induction
    (motive := fun x _ => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, x) X.vac)) ?_ ?_ ?_ gen
  · intro x hx
    rcases hx with (⟨hk, hks⟩ | ⟨k, hα⟩) | ⟨k, hα⟩
    · rw [GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum hX t e hP.1 x hk hks]
      exact vac.smul (detAlg e hP.1 x)
    · exact hecke e hP.1 ϖ k x hα
    · have hc := ((GlobalTheory.SplitPlace.split_local (stdLatSp WW hX.stdW.1) P e hP).2.2 ϖ hϖ hϖ2).2 k x⁻¹ hα |>.1
      have h2 := hecke (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1)
        ⟨star (ϖ : D.host.E), ϖ.2.map (starRingEnd D.host.E).toIntAlgHom⟩ k _ hc
      exact (congrArg (fun y : GA D WW => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, y) X.vac))
        (inv_inv x)).mp h2
  · show IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac)
    rw [map_one]
    exact vac
  · intro x y _ _ hx hy
    have e1 : ((1 : GA D A), x * y) = (1, x) * (1, y) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t 1 x hx hy
end GlobalTheory.SplitVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | exact _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination <;> assumption)
end
end

