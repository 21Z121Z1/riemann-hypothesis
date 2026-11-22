import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointMapLinearity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRoot

theorem sigR_sigR (D : D7) (w : Formalism.L2.Theta.AE D) :
    sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig w) = w := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [sigR, hσ]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem exists_idF_eq_mul_sigR (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) :
    ∃ t : (AF D.host.F)ˣ, ((idF D t : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (x : Formalism.L2.Theta.AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : Formalism.L2.Theta.AE D) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  have htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z := by
    intro z
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨t, ht⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr
    (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])
  refine ⟨t, ?_⟩
  convert congrArg Units.val ht using 1
  · rfl
  · rfl

theorem pow_eq_one_of_isDetRoot (D : D7) (V : HSp D) (g : GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ)
    (hn : 0 < n) (hbase : ∀ t, c (idF D t) ^ n = 1) (hcont : Continuous c) (hR : IsDetRoot V g x)
    (d : (Formalism.L2.Theta.AE D)ˣ) (hd : (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det)
    (hfu : Formalism.L2.Pj.FinUnit d) : ∃ N : ℕ, 0 < N ∧ c x ^ N = 1 := by
  obtain ⟨t, ht⟩ := exists_idF_eq_mul_sigR D x
  have hxx : x * x = d * idF D t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht, hd]
    unfold IsDetRoot at hR
    unfold Formalism.L2.Theta.mt
    nth_rewrite 1 [hR]
    ring
  obtain ⟨N, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hcont
  refine ⟨2 * (m * n), by positivity, ?_⟩
  rw [pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t,
    one_pow]

theorem infPart_det_of_mem_GfC : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V →
    infPart D (Formalism.L2.Theta.mt V g).det = 1 := by
  intro D V g hg
  have h : infHom V g = 1 := hg
  have h2 := congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h
  simp only [Units.val_one, Matrix.det_one] at h2
  rw [← h2]
  unfold infHom Formalism.L2.Theta.mt Formalism.UG.bc
  rw [RingHom.map_det]
  rfl

theorem finUnit_det_of_carries : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    g ∈ GfC V → finM V hn g = k.1 →
    Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat D.host.E n) (Formalism.L2.Col.stdLat D.host.E n) →
    ∃ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det ∧ Formalism.L2.Pj.FinUnit d := by
  intro D V n hn g k hg hk hc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_entries_of_carries_standardLattice D.host.F D.host.E n k hc
  have hu : IsUnit (Formalism.L2.Theta.mt V g).det := by
    unfold Formalism.L2.Theta.mt
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  obtain ⟨f1, f2⟩ := GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart D V n hn g k hk h1 h2 hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩
  rw [hu.unit_spec]
  exact infPart_det_of_mem_GfC D V g hg

end GlobalTheory.CharRoot

theorem GlobalTheory.CharRoot.chr_xr_pow_eq_one : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA j hj i hi β
  have hc : ChrEq (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a) := hA.chr ⟨j, hj⟩
  obtain ⟨hG, hF, hR⟩ := hA.kA i hi β
  have hb := hA.base i hi β

  obtain ⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by
    have hx := hI.xi_reads a
    have ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := (I.tup a).2.1.1.1.2
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    ext y
    have h1 := hx y
    simp only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]
    simp

  have hpow : ∀ k : ℕ, ChrEq (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]
      exact GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc
  have hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1 := by
    intro t
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hpow k
    rw [mul_pow, hξ, mul_one] at h1
    have h2 := GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t
    simpa using h2

  have hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) := by
    obtain ⟨h1, h2⟩ := hb
    have h := h1.lat
    erw [h2] at h
    exact h
  obtain ⟨d, hd, hfu⟩ := GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar
  exact GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  first | exact @GlobalTheory.Transport.TwistRead.qread | exact GlobalTheory.Transport.TwistRead.qread | (intros; apply GlobalTheory.Transport.TwistRead.qread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section
namespace GlobalTheory.ChainTw.UnifFree

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem mu_ratio (t t' : T) (i j : ℕ) :
    (comR R t).μ i * ((comR R t).μ j)⁻¹ = (comR R t').μ i * ((comR R t').μ j)⁻¹ := by
  show R.mu0 i * R.xi t * (R.mu0 j * R.xi t)⁻¹ = R.mu0 i * R.xi t' * (R.mu0 j * R.xi t')⁻¹
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_right_eq_div, mul_div_mul_right_eq_div]

theorem isHval_tuple {t t' : T} {S : Set (HeightOneSpectrum (𝓞 D.host.F))} {k : ℕ} {H : ℂ}
    (h : IsHval (comR R t) S k H) : IsHval (comR R t') S k H := by
  obtain ⟨Λ, h1, h2⟩ := h
  refine ⟨Λ, fun i hi => ⟨(h1 i hi).1, fun z hz => ?_⟩, h2⟩
  rw [(h1 i hi).2 z hz, mu_ratio R t t' i (k + 1)]

theorem ipTh_self {V W : HSp D} (m : Measure (WO V W)) (X : Set (WO V W)) (f : WO V W → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = ((nrm2 m X f : ℝ) : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  show f w * (starRingEnd ℂ) (f w) = _
  rw [Complex.mul_conj']
  push_cast
  ring

theorem unifY (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) (k : ℕ) (hk : k + 1 < D.R.m) :
    ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
      IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v := by
  have hk' : k < D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) k (stY R t k) := fun t => (hC t).2.1 k hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (k + 1) (stY R t (k + 1)) := fun t => (hC t).2.1 (k + 1) hk
  have hp : ∀ t, IsStep (twR R t) (k + 1) (stepY R t k) := fun t => (hC t).2.2.2.1 k hk
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D k) (Yc D (k + 1))
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM k hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D k) (Yc D (k + 1)) (GlobalTheory.Chain.expS D ⟨k, hk'⟩) (GlobalTheory.Chain.expT D ⟨k, hk'⟩) (R.ωY t k) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) k hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vY t k) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _ (R.ωY t k) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D k)), zReal (stepY R t k) m X φ v g * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      zReal (stepY R A.μ0 k) m X φ v g * (nrm2 m X (R.vY t k) : ℂ) := fun t g => by
    have e : coefW (stepY R t k).ω m X ((stepY R t k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
        coefW (stepY R A.μ0 k).ω m X ((stepY R A.μ0 k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY t k) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨k, hk'⟩ _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ (R.ωY t k) (R.ωY A.μ0 k)
        (R.vY t k) (R.vY A.μ0 k) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepY R t k) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vY t k) : ℝ) : ℂ) / (nrm2 m X (R.vY A.μ0 k) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepY R t k) m X φ v g ∂mR) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * (nrm2 m X (R.vY t k) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY A.μ0 k) : ℝ) : ℂ) (fun g => zReal (stepY R t k) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY t k) : ℝ) : ℂ) (fun g => zReal (stepY R A.μ0 k) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY A.μ0 (k + 1)) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) * ∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast ((hV A.μ0).1 (k + 1) hk).2.ne'
  · obtain ⟨hv1, hv2⟩ := (hV t).1 (k + 1) hk
    have hPi : (∏ PP ∈ R.Q t, idxQ PP (k + 1)) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).1 k hk m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP (k + 1)) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepY R t k) m X φ v g ∂mR) =
        (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY t (k + 1)) / ∏ PP ∈ R.Q t, idxQ PP (k + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) *
        ((∫ g, zReal (stepY R t k) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ)) = _
    rw [hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem unifX (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) :
    ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
      IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ)
        fun _ => v := by
  have h2 := D.R.two_le_m
  have hk' : D.R.m - 1 < D.R.m := by omega
  have e1 : D.R.m - 1 + 1 = D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1) (stY R t (D.R.m - 1)) := fun t => (hC t).2.1 _ hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1 + 1) (stX R t) := fun t => by
    rw [e1]; exact (hC t).2.2.1
  have hp : ∀ t, IsStep (twR R t) (D.R.m - 1 + 1) (stepX R h t) := fun t => by
    rw [e1]; exact (hC t).2.2.2.2
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D (D.R.m - 1)) D.sp.X'
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM _ hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D (D.R.m - 1)) D.sp.X' (GlobalTheory.Chain.expS D ⟨D.R.m - 1, hk'⟩)
      (GlobalTheory.Chain.expT D ⟨D.R.m - 1, hk'⟩) (R.ωX t) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) _ hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vX t) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ _ _ (R.ωX t) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D (D.R.m - 1))), zReal (stepX R h t) m X φ v g * (nrm2 m X (R.vX A.μ0) : ℂ) =
      zReal (stepX R h A.μ0) m X φ v g * (nrm2 m X (R.vX t) : ℂ) := fun t g => by
    have e : coefW (stepX R h t).ω m X ((stepX R h t).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX A.μ0) : ℂ) =
        coefW (stepX R h A.μ0).ω m X ((stepX R h A.μ0).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX t) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨D.R.m - 1, hk'⟩ _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ (R.ωX t)
        (R.ωX A.μ0) (R.vX t) (R.vX A.μ0) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepX R h t) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vX t) : ℝ) : ℂ) / (nrm2 m X (R.vX A.μ0) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepX R h t) m X φ v g ∂mR) * (nrm2 m X (R.vX A.μ0) : ℂ) =
      (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * (nrm2 m X (R.vX t) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX A.μ0) : ℝ) : ℂ) (fun g => zReal (stepX R h t) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX t) : ℝ) : ℂ) (fun g => zReal (stepX R h A.μ0) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) * ∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast (hV A.μ0).2.2.ne'
  · have hv1 := (hV t).2.1
    have hv2 := (hV t).2.2
    have hPi : (∏ PP ∈ R.Q t, idxQ PP D.R.m) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).2 m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP D.R.m) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepX R h t) m X φ v g ∂mR) =
        (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP D.R.m : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) / ∏ PP ∈ R.Q t, idxQ PP (D.R.m - 1 + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) *
        ((∫ g, zReal (stepX R h t) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (D.R.m - 1 + 1) : ℝ) : ℂ)) = _
    rw [e1, hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem rUnif_of : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → RealZetaQ D → Restore D → ∀ h : RangeX R, RChain R h → RMeas R → RVol R → RNrm R → RUnif R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hF hG hZ hRs h hC hM hV hN
  exact ⟨fun k hk => unifY R hF.core.lev hG hZ hRs h hC hM hV hN k hk, unifX R hF.core.lev hG hZ hRs h hC hM hV hN⟩

end GlobalTheory.ChainTw.UnifFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocProd

variable {D : D7}

theorem mem_congGrp_entries (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := fun g hg =>
  (mem_congGrp_entries V J g).2 fun i j => h ((mem_congGrp_entries V I g).1 hg i j)

theorem idAt_le_idOff (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : idAt D P ≤ idOff D P' := by
  intro a ha
  have h2 := (Submodule.mem_inf.1 ha).2
  rw [Submodule.mem_iInf] at h2
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact h2 ⟨w, fun h' => h w h' hw⟩

theorem grpAt_le_grpOff' (V : HSp D) (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : grpAt V P ≤ grpOff V P' :=
  congGrp_mono V (idAt_le_idOff P P' h)

theorem mem_idOff_of_forall (P : Pl D → Prop) (a : AE D) (h : ∀ w, P w → a ∈ idOff D (· = w)) : a ∈ idOff D P := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at h ⊢
  intro w hw
  exact h w hw w rfl

theorem mem_grpOff_of_forall (V : HSp D) (P : Pl D → Prop) (g : GA D V) (h : ∀ w, P w → g ∈ grpOff V (· = w)) :
    g ∈ grpOff V P := by
  unfold grpOff
  rw [mem_congGrp_entries]
  intro i j
  exact mem_idOff_of_forall P _ fun w hw => (mem_congGrp_entries V _ g).1 (h w hw) i j

theorem map_list_prod_eq_one {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) :
    ∀ J : List ι, (∀ i ∈ J, φ (f i) = 1) → φ (J.map f).prod = 1
  | [], _ => by simp
  | a :: J, h => by
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      map_list_prod_eq_one φ f J fun i hi => h i (List.mem_cons_of_mem a hi), one_mul]

theorem map_list_prod_single {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) (j : ι)
    (h1 : ∀ i, i ≠ j → φ (f i) = 1) : ∀ J : List ι, J.Nodup → j ∈ J → φ (J.map f).prod = φ (f j)
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: J, hn, hj => by
    obtain ⟨ha, hn'⟩ := List.nodup_cons.1 hn
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases haj : a = j
    · subst haj
      rw [map_list_prod_eq_one φ f J fun i hi => h1 i fun e => ha (e ▸ hi), mul_one]
    · have hjJ : j ∈ J := by
        rcases List.mem_cons.1 hj with e | e
        · exact absurd e.symm haj
        · exact e
      rw [h1 a haj, one_mul, map_list_prod_single φ f j h1 J hn' hjJ]

theorem eq_prod_gl_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  intro D S k _ _ _ _ ι p n _ _ β hinj J hJ hall κ
  have hloc := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).1 κ
  have hcomm := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).2.1
  choose x hx y hy hxy using hloc
  have hfr := fun i => ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 (x i)).1 (hx i)
  choose g hg using hfr
  have hglAt : ∀ i, (β i).gl (g i) ∈ grpAt S (· = (p i).v) := fun i =>
    ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 _).2 ⟨g i, rfl⟩
  have key : ∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v) := by
    intro i
    rw [← hg i, hxy i, hcomm i (x i) (hx i) (y i) (hy i), mul_assoc, mul_inv_cancel, mul_one]
    exact hy i
  refine ⟨g, key, (J.map fun i => (β i).gl (g i)).prod⁻¹ * κ, ?_, (mul_inv_cancel_left _ _).symm⟩
  apply mem_grpOff_of_forall
  rintro w ⟨j, rfl⟩
  let φ := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idOff D (· = (p j).v)))).comp (matHom S)
  have hker : ∀ h, h ∈ grpOff S (· = (p j).v) ↔ φ h = 1 := fun h => MonoidHom.mem_ker
  have hκ : φ κ = φ ((β j).gl (g j)) := by
    have := (hker _).1 (key j)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have h1 : ∀ i, i ≠ j → φ ((β i).gl (g i)) = 1 := fun i hij =>
    (hker _).1 (grpAt_le_grpOff' S _ _ (fun w hw hw' => hij (hinj (hw.symm.trans hw'))) (hglAt i))
  rw [hker, map_mul, map_inv, map_list_prod_single φ (fun i => (β i).gl (g i)) j h1 J hJ (hall j), hκ, inv_mul_cancel]

end GlobalTheory.FinPl.LocProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  first | exact @GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | exact GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | (intros; apply GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit <;> assumption)
end

