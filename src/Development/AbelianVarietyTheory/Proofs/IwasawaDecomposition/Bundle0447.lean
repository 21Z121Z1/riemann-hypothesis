import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem cTw_eq_mul (B : Base) :
    ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := B.R.t_odd
  have h2 : B.R.t + 1 = 2 * (b + 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  ring

theorem trueWeight_lastStep_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = B.wts.lamTrue u B.R.m τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (Examples₂.lamOf (B.hcW u τ) B.R.m) (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (Examples₂.lamOf (B.hcW u τ) B.R.m) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

theorem trueRowWeight_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = B.wts.sgTrue τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (B.wts.row τ).sg (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (B.wts.row τ).sg (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

theorem branchingNorm_identity_trueColumns_members {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    BeOnTie (I.rec7 l Z) u := by
  intro τ
  have e1 := trueWeight_lastStep_trueColumns I l Z u τ
  have e2 := trueRowWeight_trueColumns I l Z u τ
  have n1 : (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW :=
    Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  have n2 : (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).sg τ).natW := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  show fockOpNorm (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)) =
    fockOpNorm (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ) (((I.rec7 l Z).fm u).sg τ)
      (Formalism.L2.Ker.brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
  rw [e1, e2] at *
  exact fockOpNorm_congr _ n1 n2

theorem beOnTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)), ∀ u, BeOnTie (I.rec7 l Z) u :=
  fun I _ _ l Z u => branchingNorm_identity_trueColumns_members I l Z u

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChainStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_tied_top_level_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (Ch : Type) (chOf : (I.stp u I.mu0 (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u I.mu0 (B.R.m - 1) c.1))), I.IdG l Z G → I.ReadsK l Z u I.mu0 (B.R.m - 1) (Nat.sub_le _ _) chOf K → ∃ (J : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (B.T u) B.R.f (badG (I.rec7 l Z))) (lamJ : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v →* ℂˣ) (V : GLevH J G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v) lamJ) (Yb : Type) (_ : Finite Yb) (_ : MulAction J.U Yb) (yb : Ch → Yb), (∀ j v h, V.fr j v h = 1) ∧ (∀ j v h M, ((lamJ j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t (B.R.m - 1) M.1.1) ∧ (∀ y : Yb, ∃! β, ∃ κ : J.U, κ • yb β = y) ∧ ∀ β, (K β).lev.Lb = J.Lb ∧ (K β).lev.U ≤ J.U ∧ (∀ κ : J.U, κ.1 ∈ (K β).lev.U ↔ κ • yb β = yb β) ∧ ∀ (κ : (K β).lev.U) (κ' : J.U), κ.1 = κ'.1 → (K β).lev.chi κ = J.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.OneLevel.stepBefore_oneLevel | exact GlobalTheory.Mem.Col2.OneLevel.stepBefore_oneLevel | (intros; apply GlobalTheory.Mem.Col2.OneLevel.stepBefore_oneLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.KerVal

theorem fm_succ_mem_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hBs hUnf hJets u μ i hi x c'
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam : ∀ j τ, Col2.lamT (B.hcW u) j τ = lamTG ((I.tw l l0 Z).fm u μ) j τ := by
    intro j τ
    unfold Col2.lamT lamTG
    show Col2.shW _ _ = Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) j) _
    obtain ⟨c, hc⟩ := B.R.t_odd
    have h1 : (B.R.t + 1) / 2 = c + 1 := by omega
    have h2 : j * (B.R.t + 1) / 2 = j * (c + 1) := by
      rw [show j * (B.R.t + 1) = 2 * (j * (c + 1)) by rw [hc]; ring]; omega
    simp only [Col2.shW, Formalism.L2.Forms.shW]
    congr 1
    funext r
    show _ + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)) = _ - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [h1, h2]
    push_cast
    ring
  have hP : ((x.1 c').1 : Formalism.L2.DIV.Pol B.LL (Tau B.R) (B.R.N (i + 1))) ∈ polV (I.rec7 l Z) u (i + 1) := by
    have h1 := VV_le_WtPol (K := B.LL) (Col2.lamT (B.hcW u) (i + 1)) (x.1 c').2
    have e : (fun τ r => (Col2.lamT (B.hcW u) (i + 1) τ).natW r) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
      funext τ r
      rw [hlam]
      refine (hnat τ r).trans ?_
      congr 1
      funext τ' r'
      exact hw τ' r'
    rw [e] at h1
    exact h1
  refine ⟨Submodule.Quotient.mk ⟨_, hP⟩, ?_⟩
  funext y
  show evP O u μ (i + 1) ⟨_, hP⟩ y = _
  show (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
    GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL (x.1 c').1) ((O u μ).frm (i + 1) y) = _
  simp only [(O u μ).frm_de (i + 1) hi y]
  rw [hStd.frm u μ (i + 1) y]
  show _ = Formalism.L2.Col.evFr (gramC (1 : Matrix (Fin _) (Fin _) _) (embAt B.embLL B.tauLL)) (shiftOf (Col2.lamT (B.hcW u) (i + 1))) B.embLL (x.1 c').1 y
  refine Eq.trans ?_ (Formalism.L2.Col.evFr_apply _ _ _ _ _).symm
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    exact ((congrArg DomWeight.detShift (hlam (i + 1) τ)).trans (hds τ)).symm
  · exact GlobalTheory.PdvKm.evFr_map _ _ _ _

end GlobalTheory.Mem.KerVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReductionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPoint_eq_of_deco_and_cosetReduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | exact GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | (intros; apply GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompanionCrd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.MemLat

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_N_iff (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal)
    (hcop : IsCoprime π (cO E π)) (x : Sp E n) :
    x ∈ d.N ↔ ∃ a ∈ d.L, ∃ b ∈ d.Lsh, x = a + cO E π • b := by
  constructor
  · intro hx
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • (π • x), d.L.smul_mem s (hd.smul_N_mem_L hmem hx), t • x, d.Lsh.smul_mem t (hd.N_le_Lsh hx), ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (cO E π) t, hst, one_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact d.N.add_mem (hd.L_le_N ha) (hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact hmem P) hb)

theorem std_of_gram (S : HSpace E) {m : ℕ} (h : S.rank = m) (hg : S.gram.reindex (finCongr h) (finCongr h) = 1) (x y : S.V) :
    stdH E m (Crd.co S h x) (Crd.co S h y) = S.hT x y := by
  subst h
  have hg' : ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hg a) b
    simpa [HSpace.gram, Matrix.one_apply] using this
  conv_rhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.sum_apply, hg',
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [stdH, Crd.co, starRingEnd_apply]

omit [NumberField E] in
theorem hStd_eq_stdH (x y : Fin n → E) : hStd E n x y = stdH E n x y := rfl

theorem mem_dual_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (b : S.V) :
    b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) (L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rw [mem_dual]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro H z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have := H a ha
    simpa [hStd_eq_stdH, hco] using this
  · intro H a ha
    have := H (co a) ⟨a, ha, rfl⟩
    simpa [hStd_eq_stdH, hco] using this

theorem companion_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (d : Deco E n ST SG) (hd : d.Ok)
    (hL : L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = d.L)
    (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) (y : S.V) :
    co y ∈ d.N ↔ ∃ a ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = a + star (algebraMap (𝓞 E) E π) • b := by
  have hA : ∀ a, a ∈ L ↔ co a ∈ d.L := fun a => by
    rw [← hL]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨z, hz, e⟩ => co.injective e ▸ hz⟩
  have hB : ∀ b, b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ d.Lsh := fun b => by
    rw [mem_dual_crd S co hco, hL]
    exact Iff.rfl
  have hc : ∀ v : Fin n → E, cO E π • v = star (algebraMap (𝓞 E) E π) • v := fun v => by
    rw [← algebraMap_smul E (cO E π) v, algebraMap_cO]
  rw [mem_N_iff d hd π hmem hcop]
  constructor
  · rintro ⟨a', ha', b', hb', e⟩
    refine ⟨co.symm a', (hA _).2 (by simpa using ha'), co.symm b', (hB _).2 (by simpa using hb'), co.injective ?_⟩
    rw [map_add, map_smul, co.apply_symm_apply, co.apply_symm_apply, e, hc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨co a, (hA a).1 ha, co b, (hB b).1 hb, ?_⟩
    rw [map_add, map_smul, hc]

end Gen

end GlobalTheory.Mem.Col2.MemLat

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.memLatAt_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (O : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).mem u).C), (∀ i c, (O.lat i c).1 = ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) → MemLatAt O (X.piT u) := by
  intro B X I hI hP l Z u O hlat
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  intro i hi
  obtain ⟨hg, hl0, hL⟩ := hsp i hi
  have hL' := (hL u I.mu0).1
  set co := GlobalTheory.Mem.Col2.Crd.co ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) with hco
  have hiso := GlobalTheory.Mem.Col2.MemLat.std_of_gram _ _ hg
  refine ⟨co, hiso, ?_, ?_⟩
  · intro y
    rw [O.lattice_integral_coordinates]
    have h1 : co y ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ y ∈ ((I.rec7 l Z).sp.X i).L0 :=
      ⟨fun ⟨z, hz, e⟩ => co.injective e ▸ hz, fun h => ⟨y, h, rfl⟩⟩
    rw [← h1, hl0]
    refine forall_congr' fun k => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r
  · intro c y
    rw [hlat i c]
    have hsep := sepElt_of_ok l.pr u
    have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
      have := hsep.conj P
      rwa [cO_cO] at this
    have hLm : ((I.rec7 l Z).clsLat u i c).map ((co : ((I.rec7 l Z).sp.X i).V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) =
        (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hL' c
    refine (GlobalTheory.Mem.Col2.MemLat.companion_crd _ co hiso _ (((I.stp u I.mu0 i).rep c).1.1.deco).1 (((I.stp u I.mu0 i).rep c).1.1.deco).2
      hLm ((B.primes X).piT u) hmem (l.pr.piT_cop u) y).trans ?_
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetCongrIndexFramesLocalLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_congr_index_frames_localLattices : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_congr | exact GlobalTheory.Mem.Col2.cosetIn_congr | (intros; apply GlobalTheory.Mem.Col2.cosetIn_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_eq_iff_reduction_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq | exact GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq | (intros; apply GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesRationalActionEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_rational_action_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_act_rat | exact GlobalTheory.Mem.Col2.cosetIn_act_rat | (intros; apply GlobalTheory.Mem.Col2.cosetIn_act_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMulStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG E ST), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  first | exact @GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | exact GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | (intros; apply GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ClsBij

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem ratAd_mem_ratPts (hc : CMData F E) (γ : UF E n) :
    ratAd F γ ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨ufGL E n γ, ?_, rfl⟩
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ

theorem exists_ratAd_eq (hc : CMData F E) {g : GL (Fin n) (AfE F E)}
    (hg : g ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ γ : UF E n, ratAd F γ = g := by
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨ratEquiv hc n ⟨r, hr⟩, ?_⟩
  show Formalism.UG.bc _ (ufGL E n _) = _
  rw [GlobalTheory.Mem.Col2.RatMove.ufGL_eq hc, MulEquiv.symm_apply_apply]

end SlopeTestRemainingChoices

theorem classes_bijective : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q C Λ Θ s U k' y hU hk' hlev hdense hpt hinj hsurj
  constructor
  · intro c c' hcc
    obtain ⟨γ, hγ, u, hu, he⟩ := (DoubleCoset.eq _ _ (y c) (y c')).1 hcc
    have he' : (y c').1 = γ.1 * (y c).1 * u.1 := by rw [he]; rfl
    obtain ⟨δ, hδ⟩ := exists_ratAd_eq hc (Subgroup.mem_subgroupOf.1 hγ)
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q δ⁻¹ _ _ (hpt c')
    have e1 : ratAd F δ⁻¹ * ((y c').1 * k') = (y c).1 * u.1 * k' := by
      rw [he', ← hδ, ← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e1] at h1
    obtain ⟨h, θ, hhθ⟩ := (hlev (y c).1 u.1 (s c) _ (hpt c) h1).1 (Subgroup.mem_subgroupOf.1 hu)
    refine hinj c c' δ h θ ?_
    have e2 : ((δ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) =
        ((δ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) * ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) := by
      simp
    rw [e2, mul_smul, hhθ, smul_smul]
    have e3 : ((δ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) * ((δ⁻¹, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) = 1 := by
      simp
    rw [e3, one_smul]
  · intro q
    induction q using Quotient.inductionOn' with
    | h z =>
    obtain ⟨x, hx, p, hp⟩ := hdense z.1 z.2
    obtain ⟨c, γ, h, θ, hcp⟩ := hsurj p
    refine ⟨c, ?_⟩
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ⁻¹ _ _ hp
    have e1 : ((γ⁻¹, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p =
        ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c := by
      rw [← hcp, smul_smul]
      congr 1
      simp
    rw [e1] at h1
    have e2 : ratAd F γ⁻¹ * (z.1 * x * k') = (y c).1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x) * k' := by
      group
    rw [e2] at h1
    have hx' : (y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x ∈ U := (hlev (y c).1 _ (s c) _ (hpt c) h1).2 ⟨h, θ, rfl⟩
    let kk : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
      ⟨(y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹, hU (mul_mem hx' (inv_mem hx))⟩
    show DoubleCoset.mk _ _ (y c) = DoubleCoset.mk _ _ z
    refine (DoubleCoset.eq _ _ (y c) z).2 ⟨z * kk⁻¹ * (y c)⁻¹, ?_, kk, Subgroup.mem_subgroupOf.2 (mul_mem hx' (inv_mem hx)), by group⟩
    rw [Subgroup.mem_subgroupOf]
    have e4 : ((z * kk⁻¹ * (y c)⁻¹ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (AfE F E))
        = ratAd F γ := by
      show z.1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹)⁻¹ * (y c).1⁻¹ = _
      rw [← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e4]
    exact ratAd_mem_ratPts hc γ

end GlobalTheory.Mem.Col2.ClsBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

structure StdKerTie {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

namespace StdKerEmpty

theorem detId_std_bot (D : D7) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D 2) (⊥ : Submodule (𝓞 D.host.E) (Fin 2 → D.host.E)) = ⊥ := by
  refine le_bot_iff.1 (Submodule.span_le.2 ?_)
  rintro _ ⟨A, hA, rfl⟩
  have hA0 : A = 0 := by
    ext i j
    have h1 : (Pi.single j 1 : Fin 2 → D.host.E) ∈ StandardLatticesGL3.stdL D 2 := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := congrFun ((Submodule.mem_bot _).1 (hA _ h1)) i
    simpa [Matrix.mulVec_single] using h2
  subst hA0
  simp

theorem not_N1_bot (D : D7) : ¬ TaylorLogMetric.N1 D ⊥ := by
  rintro ⟨b, -, hb⟩
  rw [Submodule.bot_mul] at hb
  have h1 : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.2 ⟨1, by simp⟩
  rw [← hb, Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem seam_lat_bot {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : s.lat (⊥ : Submodule (𝓞 X.E) (Sp X.E n)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot] at hx
  subst hx
  funext i
  simp

theorem chiRec_bot (D : D7) (idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D) (h : TaylorLogMetric.RelDetPinned D idl) : TaylorLogMetric.chiRec D idl ⊥ = 0 := by
  unfold TaylorLogMetric.chiRec
  rw [dif_neg]
  exact fun hx => not_N1_bot D ((h.2.1 ⊥).2 hx)

theorem not_heq_amb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex)
    (hXe : t.X = B.fields) : ¬ HEq t.amb I.A := by
  intro h
  have key : ∀ (X' : Fields) (s : Seam (I.rec7 l Z) X') (hX : X' = B.fields),
      HEq (ambOf s t.B t.χ t.cD) I.A → False := by
    intro X' s hX hh
    subst hX
    have e := congrArg (fun A : Amb B.fields => A.chiF 2 2 ⊥ ⊥) (eq_of_heq hh)
    simp only [ambOf] at e
    have hl : Base.chiFac t.χ 2 2 (⊥ : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin 2 → (I.rec7 l Z).host.E)) ⊥ = 0 := by
      simp [Base.chiFac, t.χ_rec, detId_std_bot, chiRec_bot _ _ t.idl_ok]
    have hr : (I.A).chiF 2 2 ⊥ ⊥ = 1 := by
      simp only [ColIn.A, AmbIn.amb, Th.chiFac]
      have hc := chiId_ne_zero I.C.chiPsi (Th.detId B.host (Th.stdL B.host 2) ⊥)
      simp [ColIn.chi, hc]
    rw [seam_lat_bot, hl, hr] at e
    exact zero_ne_one e
  exact key t.X t.seam hXe h

end StdKerEmpty

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRowStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondElement_integral_support_lastRow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  first | exact @GlobalTheory.Mem.Dil.dia_data | exact GlobalTheory.Mem.Dil.dia_data | (intros; apply GlobalTheory.Mem.Dil.dia_data <;> assumption)
end

