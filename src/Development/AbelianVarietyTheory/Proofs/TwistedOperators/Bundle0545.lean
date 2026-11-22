import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.FlipStart.Col

variable {D : D7}

theorem fund_exch {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] {Fd Fd' : Set (GA D V)}
    (h1 : IsFundamentalDomain (GQ V) Fd μ) (h2 : IsFundamentalDomain (GQ V) Fd' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f Fd μ ↔ IntegrableOn f Fd' μ) ∧ ∫ g in Fd, f g ∂μ = ∫ g in Fd', f g ∂μ := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact ⟨h1.integrableOn_iff h2 fun γ g => hf γ γ.2 g, h1.setIntegral_eq h2 fun γ g => hf γ γ.2 g⟩

theorem step_heq {S S₀ T T₀ : HSp D} (hS : S = S₀) (hT : T = T₀)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {ω₀ : GA D S₀ × GA D T₀ →* Module.End ℂ (WO S₀ T₀ → ℂ)} (hω : HEq ω ω₀)
    {s : WO S T → ℂ} {s₀ : WO S₀ T₀ → ℂ} (hs : HEq s s₀)
    {μ : Measure (GA D T)} {μ₀ : Measure (GA D T₀)} (hμ : HEq μ μ₀) (hH : μ₀.IsHaarMeasure)
    {Fd : Set (GA D T)} {Fd₀ : Set (GA D T₀)} (h1 : IsFundamentalDomain (GQ T) Fd μ) (h2 : IsFundamentalDomain (GQ T₀) Fd₀ μ₀)
    {F : GA D T → ℂ} {F₀ : GA D T₀ → ℂ} (hF : HEq F F₀)
    (hinv : ∀ h, ∀ γ ∈ GQ T₀, ∀ g, thetaKO ω₀ h (γ * g) s₀ * F₀ (γ * g) = thetaKO ω₀ h g s₀ * F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO ω₀ h g s₀ * F₀ g) Fd₀ μ₀) :
    (∀ h, IntegrableOn (fun g => thetaKO ω h g s * F g) Fd μ) ∧
      HEq (fun h => ∫ g in Fd, thetaKO ω h g s * F g ∂μ) (Lift.liftInt μ₀ Fd₀ (thetaKO ω₀) s₀ F₀) := by
  subst hS hT
  obtain rfl := eq_of_heq hω
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hμ
  obtain rfl := eq_of_heq hF
  haveI := hH
  exact ⟨fun h => (fund_exch h1 h2 _ (hinv h)).1.2 (hint h),
    heq_of_eq (funext fun h => (fund_exch h1 h2 _ (hinv h)).2)⟩

theorem pt_heq {ψ ψ₀ : AddChar (AF D.host.F) ℂ} {θ θ₀ : InfFam D} (hψ : ψ = ψ₀) (hθ : θ = θ₀) {S S₀ T T₀ : HSp D} (hS : S = S₀)
    (hT : T = T₀)
    {a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ} (ha : HEq a a₀)
    {b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {b₀ : D.what₂.Tau → Matrix (Fin T₀.rank) (Fin T₀.rank) ℂ} (hb : HEq b b₀)
    {c : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ} (hc : HEq c c₀)
    {d : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {d₀ : D.what₂.Tau → Matrix (Fin T₀.rank) (Fin T₀.rank) ℂ} (hd : HEq d d₀)
    {f : WO S T → ℂ} {f₀ : WO S₀ T₀ → ℂ} (hf : HEq f f₀) {P : PolF D T.rank S.rank} {P₀ : PolF D T₀.rank S₀.rank} (hP : HEq P P₀) :
    HEq (pureTensorO ψ θ S T a b c d f P) (pureTensorO ψ₀ θ₀ S₀ T₀ a₀ b₀ c₀ d₀ f₀ P₀) := by
  subst hψ hθ hS hT
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hP
  rfl

theorem measFD_heq {V V₀ : HSp D} (hV : V = V₀) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  subst hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : V = V₀) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  subst hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (fun _ _ e => e.1) h.1 h₀.1)

theorem cast_fun_heq {A B : Type} (e : A = B) (φ : B → ℂ) : HEq (fun x => φ (cast e x)) φ := by
  subst e; rfl

variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem stepY {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T} {M : Vol ch.G} (hM : M.Is t)
    {j : ℕ} (hj : j + 1 < D.R.m) {fj : Sch ch.G (.down t 0 j)} (hfj : HEq fj (R.vY t j))
    {P : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} {P₀ : PolF D (Yc D (j + 1)).rank (Yc D j).rank}
    (hP : HEq P P₀) {s : Sch ch.G (.down t 0 j)} (hs : s = ch.W.fock (.mu t 0 j) fj P) {F : Fn ch.G (.grid 0 (j + 1))}
    {F₀ : GA D (Yc D (j + 1)) → ℂ} (hF : HEq F F₀)
    (hinv : ∀ γ ∈ GQ (Yc D (j + 1)), ∀ g, F₀ (γ * g) = F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO (R.ωY t j) h g (R.ptY t j P₀) * F₀ g) (R.fdY t (j + 1)) (R.νY t (j + 1))) :
    LiftConv ch.W M (.down t 0 j) s F ∧
      HEq (liftA ch.W M (.down t 0 j) s F)
        (Lift.liftInt (R.νY t (j + 1)) (R.fdY t (j + 1)) (thetaKO (R.ωY t j)) (R.ptY t j P₀) F₀) := by
  subst hs
  have hS : ch.G.V (.grid 0 j) = Yc D j := congrArg LSp.sp (colY_lt R.toLevCh (by omega))
  have hT : ch.G.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh hj)
  have hs : HEq (ch.W.fock (.mu t 0 j) fj P) (R.ptY t j P₀) :=
    pt_heq hW.ψ hW.θ hS hT (hW.cartY j (by omega)) (hW.cartY (j + 1) hj) (hW.onbY j (by omega)) (hW.onbY (j + 1) hj) hfj hP
  have hAt := hM.vtx (.grid 0 (j + 1)) ⟨Nat.zero_le _, by omega⟩
  have hfund := hAt.haar_fund
  have hK : HEq (levJ ch.G t (.grid 0 (j + 1)))
      (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t hj
  have key : HEq (M.ν (.grid 0 (j + 1))) (R.νY t (j + 1)) ∧ (R.νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) (R.fdY t (j + 1)) (R.νY t (j + 1)) := by
    unfold Vol.IsAt at hAt
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have hc := hmod.νY t (j + 1) h
      rw [if_neg (show ¬ (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hT hK hAt hc, hc.1.1, hc.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      have hc := hmod.νY' t
      rw [← e] at hc
      rw [if_pos (show (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hT hK hAt hc, hc.1.1, hc.2⟩
  have hker := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ (R.ωY t j) (hch.ωY t j hj) _ (hch.ptY t j hj P₀)).1
  exact step_heq hS hT (hW.omY t j hj) hs key.1 key.2.1 hfund.2 key.2.2 hF (fun h γ hγ g => by
      have h1 := hker 1 (one_mem _) γ hγ h g
      rw [one_mul] at h1
      rw [h1, hinv γ hγ g]) hint

theorem stepX {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T} {M : Vol ch.G} (hM : M.Is t)
    {j : ℕ} (hj : j + 1 = D.R.m) {fj : Sch ch.G (.down t 0 j)} (hfj : HEq fj (R.vX t))
    {P : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} {P₀ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank}
    (hP : HEq P P₀) {s : Sch ch.G (.down t 0 j)} (hs : s = ch.W.fock (.mu t 0 j) fj P) {F : Fn ch.G (.grid 0 (j + 1))}
    {F₀ : GA D D.sp.X' → ℂ} (hF : HEq F F₀)
    (hinv : ∀ γ ∈ GQ D.sp.X', ∀ g, F₀ (γ * g) = F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO (R.ωX t) h g (R.ptX t P₀) * F₀ g) (R.fdX t) (R.νX t)) :
    LiftConv ch.W M (.down t 0 j) s F ∧
      HEq (liftA ch.W M (.down t 0 j) s F)
        (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t P₀) F₀) := by
  subst hs
  have e : D.R.m - 1 = j := by omega
  have hS : ch.G.V (.grid 0 j) = Yc D (D.R.m - 1) := by
    rw [e]; exact congrArg LSp.sp (colY_lt R.toLevCh (by omega))
  have hT : ch.G.V (.grid 0 (j + 1)) = D.sp.X' := by
    show (columnBlock R.toLevCh (j + 1)).sp = _
    rw [hj, colY_m]
  have hcS : HEq (ch.W.cart (.grid 0 j)) (cart (R.MY (D.R.m - 1))) := by
    rw [e]; exact hW.cartY j (by omega)
  have hoS : HEq (ch.W.onb (.grid 0 j)) (onb (R.MY (D.R.m - 1))) := by
    rw [e]; exact hW.onbY j (by omega)
  have hcT : HEq (ch.W.cart (.grid 0 (j + 1))) (cart R.MX) := by
    rw [hj]; exact hW.cartX
  have hoT : HEq (ch.W.onb (.grid 0 (j + 1))) (onb R.MX) := by
    rw [hj]; exact hW.onbX
  have hs : HEq (ch.W.fock (.mu t 0 j) fj P) (R.ptX t P₀) := pt_heq hW.ψ hW.θ hS hT hcS hcT hoS hoT hfj hP
  have hAt := hM.vtx (.grid 0 (j + 1)) ⟨Nat.zero_le _, by omega⟩
  have hfund := hAt.haar_fund
  have hK : HEq (levJ ch.G t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) :=
    levCol_top R.toLevCh t (by omega)
  unfold Vol.IsAt at hAt
  rw [if_pos (show (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
  have hc := hmod.νX t
  have hker := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ (R.ωX t) (hch.ωX t) _ (hch.ptX t P₀)).1
  exact step_heq hS hT (hW.omX t j hj) hs (measDef_heq hT hK hAt hc) hc.1.1 hfund.2 hc.2 hF (fun h γ hγ g => by
      have h1 := hker 1 (one_mem _) γ hγ h g
      rw [one_mul] at h1
      rw [h1, hinv γ hγ g]) hint

theorem col_ind {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) : ∀ n, n + 1 ≤ D.R.m → ∀ (g : ∀ j : Fin n, Sch ch.G (.down t 0 j)),
    (∀ j : Fin n, ∃ fj, HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j)) →
    ∀ (F : Fn ch.G (.grid 0 n)) (F₀ : R.CC t n) (v : SmT (R.MY n)), HEq F (F₀.1 v) →
    PathConv ch.W M (downPath t 0 n) (downFam t 0 n g) F ∧
      HEq (liftP ch.W M (downPath t 0 n) (downFam t 0 n g) F) (ch.cv.dnFun t n (F₀.1 v))
  | 0, _, _, _, _, _, _, hF => ⟨trivial, hF⟩
  | n + 1, hn, g, hg, F, F₀, v, hF => by
    obtain ⟨fj, hfj, hgj⟩ := hg (Fin.last n)
    have hgj' : g (Fin.last n) = ch.W.fock (.mu t 0 n) fj (q n) := hgj
    have hio := hch.ioY t n (by omega)
    have hst := stepY hW hch hmod hM (j := n) (by omega) hfj ((hq n).1 (by omega)) hgj' hF
      (fun γ hγ g' => (GlobalTheory.ChainEquiv.multT_value _ _ _ _ F₀.1 F₀.2 v).1 γ hγ g') (fun h => hio.integ F₀ _ v h)
    have e1 : Lift.liftInt (R.νY t (n + 1)) (R.fdY t (n + 1)) (thetaKO (R.ωY t n)) (R.ptY t n (ch.cv.polY n)) (F₀.1 v) =
        (R.ioY t n F₀).1 (R.ItY n (ch.cv.polY n) v) := funext fun g' => hio.eq F₀ _ v g'
    rw [e1] at hst
    have ih := col_ind hW hch hmod hq hM n (by omega) (fun j => g j.castSucc) (fun j => hg j.castSucc) _ (R.ioY t n F₀)
      (R.ItY n (ch.cv.polY n) v) hst.2
    refine ⟨(pathConv_comp ch.W M (Path.one (.down t 0 n)) ((), g (Fin.last n)) F (downPath t 0 n)
      (downFam t 0 n fun j => g j.castSucc)).2 ⟨⟨trivial, hst.1⟩, ih.1⟩, ?_⟩
    refine HEq.trans (heq_of_eq (pathLift_comp ch.W M (Path.one (.down t 0 n)) ((), g (Fin.last n)) F (downPath t 0 n)
      (downFam t 0 n fun j => g j.castSucc))) ?_
    refine ih.2.trans (heq_of_eq ?_)
    show _ = ch.cv.dnFun t n _
    rw [e1]

theorem formX_inv (hmod : R.IsModels) (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    ∀ γ ∈ GQ D.sp.X', ∀ g, d.formX t y (γ * g) = d.formX t y g := by
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ := SetLike.le_def.1 (hmod.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have := GlobalTheory.ThetaIntegrand.ext_invariant R.cX hmem
  intro γ hγ g
  unfold ChainVec.formX
  simp only [CoefA.toMap, LinearMap.coe_mk, AddHom.coe_mk, this γ hγ g]

theorem col_ind' {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) {n n' : ℕ} (hn : n = n') (hn1 : n + 1 ≤ D.R.m) (g : ∀ j : Fin n, Sch ch.G (.down t 0 j))
    (hg : ∀ j : Fin n, ∃ fj, HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j))
    (F : Fn ch.G (.grid 0 n)) (F₀ : R.CC t n') (v : SmT (R.MY n')) (hF : HEq F (F₀.1 v)) :
    PathConv ch.W M (downPath t 0 n) (downFam t 0 n g) F ∧
      HEq (liftP ch.W M (downPath t 0 n) (downFam t 0 n g) F) (ch.cv.dnFun t n' (F₀.1 v)) := by
  subst hn
  exact col_ind hW hch hmod hq hM n hn1 g hg F F₀ v hF

theorem col_top {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) (y : (R.HX t).H) : ∀ N, N = D.R.m → ∀ (g : ∀ j : Fin N, Sch ch.G (.down t 0 j)),
    (∀ j : Fin N, ((j : ℕ) + 1 < D.R.m → ∃ fj, HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j)) ∧
      ((j : ℕ) + 1 = D.R.m → ∃ fj, HEq fj (R.vX t) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j))) →
    ∀ F : Fn ch.G (.grid 0 N), HEq F (ch.cv.formX t y) →
    PathConv ch.W M (downPath t 0 N) (downFam t 0 N g) F ∧
      HEq (liftP ch.W M (downPath t 0 N) (downFam t 0 N g) F) (ch.cv.lift t y)
  | 0, h, _, _, _, _ => absurd h (by have := D.R.two_le_m; omega)
  | k + 1, hk, g, hg, F, hF => by
    obtain ⟨fj, hfj, hgj⟩ := (hg (Fin.last k)).2 (by simp only [Fin.val_last]; omega)
    have hgj' : g (Fin.last k) = ch.W.fock (.mu t 0 k) fj (q k) := hgj
    have hio := hch.ioX t
    have hst := stepX hW hch hmod hM (j := k) (by omega) hfj ((hq k).2 (by omega)) hgj' hF (formX_inv hmod ch.cv t y)
      (fun h => hio.integ ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) ch.cv.polX ch.cv.v h)
    have e1 : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t ch.cv.polX) (ch.cv.formX t y) =
        (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX ch.cv.polX ch.cv.v) :=
      funext fun g' => hio.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) ch.cv.polX ch.cv.v g'
    rw [e1] at hst
    have ih := col_ind' hW hch hmod hq hM (n := k) (n' := D.R.m - 1) (by omega) (by omega) (fun j => g j.castSucc)
      (fun j => (hg j.castSucc).1 (by have := j.2; simp only [Fin.coe_castSucc]; omega)) _
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)) (R.ItX ch.cv.polX ch.cv.v) hst.2
    refine ⟨(pathConv_comp ch.W M (Path.one (.down t 0 k)) ((), g (Fin.last k)) F (downPath t 0 k)
      (downFam t 0 k fun j => g j.castSucc)).2 ⟨⟨trivial, hst.1⟩, ih.1⟩, ?_⟩
    refine HEq.trans (heq_of_eq (pathLift_comp ch.W M (Path.one (.down t 0 k)) ((), g (Fin.last k)) F
      (downPath t 0 k) (downFam t 0 k fun j => g j.castSucc))) ?_
    refine ih.2.trans (heq_of_eq ?_)
    exact (congrArg (ch.cv.dnFun t (D.R.m - 1)) e1).symm

end GlobalTheory.FlipStart.Col

open GlobalTheory.FlipStart GlobalTheory.FlipStart.Col in

theorem GlobalTheory.FlipStart.column : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  intro _ _
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t f q hf hq M hM y
  have h := col_top hch.weil s.core.chain s.core.models hq hM y D.R.m rfl (fun j => ch.W.fock (.mu t 0 j) (f j) (q j))
    (fun j => ⟨fun h => ⟨f j, (hf j).1 h, rfl⟩, fun h => ⟨f j, (hf j).2 h, rfl⟩⟩) (formTop ch t y)
    (by unfold formTop; exact cast_fun_heq _ _)
  exact ⟨h.1, eq_of_heq h.2⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ i : ℕ, IsSelfDualC V (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) ∧ (∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) ∧ ∀ 𝔪 : Ideal (𝓞 D.host.E), congLev D.sp.cm V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) 𝔪 = congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | exact GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | (intros; apply GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finset_sum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | exact GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | (intros; apply GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realActionOnVertexWeight_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  first | exact @GlobalTheory.RealActCont.realAct_inv_continuous | exact GlobalTheory.RealActCont.realAct_inv_continuous | (intros; apply GlobalTheory.RealActCont.realAct_inv_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_harishChandra : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.ArchRec.itLine_of_hypotheses | exact GlobalTheory.ArchRec.itLine_of_hypotheses | (intros; apply GlobalTheory.ArchRec.itLine_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  first | exact @GlobalTheory.ParIndex.relIndex_levV_latLev | exact GlobalTheory.ParIndex.relIndex_levV_latLev | (intros; apply GlobalTheory.ParIndex.relIndex_levV_latLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  first | exact @GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | exact GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | (intros; apply GlobalTheory.HalfSplit.relIndex_nsmul_half_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  first | exact @GlobalTheory.HalfIndex.relIndex_nsmul_half | exact GlobalTheory.HalfIndex.relIndex_nsmul_half | (intros; apply GlobalTheory.HalfIndex.relIndex_nsmul_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainStepsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  first | exact @GlobalTheory.SepRows.weakSep_of_steps | exact GlobalTheory.SepRows.weakSep_of_steps | (intros; apply GlobalTheory.SepRows.weakSep_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_eq_thetaLift_definiteGroup_form : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  first | exact @GlobalTheory.TraceLift.exists_thF_eq_thetaKO | exact GlobalTheory.TraceLift.exists_thF_eq_thetaKO | (intros; apply GlobalTheory.TraceLift.exists_thF_eq_thetaKO <;> assumption)
end

