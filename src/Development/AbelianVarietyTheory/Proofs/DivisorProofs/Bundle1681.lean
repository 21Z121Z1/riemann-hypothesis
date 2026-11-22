import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

theorem mu_detAt_eq_levChi {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0)
    (hQ : L.Q t = ∅) {P : Finset (Pl D.host.E)} {e : AE D} (hee : e * e = e)
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) {κ : GA D (Vc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 κ) :
    ((L.mu t ((i : ℕ) + 1) (detAt e hee _ κ) : Circle) : ℂ) = levChi _ (L.βV i) (flagL (L.datVt i t)) κ := by
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have one : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) = 1 := fun PP h =>
    congrFun hκ.2.2 ⟨PP, h⟩
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  have mV := (mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP).1
  rw [levChi_flag_V i t tg, mV, hQ, Finset.prod_empty, Finset.prod_empty, one_mul]
  refine congrArg (fun z : ℂˣ => ((z * 1 : ℂˣ) : ℂ)) (Finset.prod_congr rfl fun PP h => ?_)
  rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (blockTri_blkOf_le _ _ (tg PP h)), one PP h, map_one, one_mul]

theorem smul_of_splitFac {D : D7} {X ι : Type} {u v : X → ℂ} {c : ι → ℂ} {μ η : (AE D)ˣ →* Circle} {x y : (AE D)ˣ} {z : ℂ}
    (h : (∏ i ∈ (∅ : Finset ι), c i) • u = ((splitFacO μ (μ * η⁻¹) x y : Circle) : ℂ) • v) (hy : y = 1) (hη : η x = 1)
    (hz : ((μ x : Circle) : ℂ) = z) : u = z⁻¹ • v := by
  rwa [Finset.prod_empty, one_smul, splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, hη, inv_one, mul_one, hy, map_one,
    mul_one, Circle.coe_inv, hz] at h

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSixth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Rebase

open GlobalTheory.ConjLiftUnique

theorem rebase_gen {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hO : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (onb M τ) (p τ))
    (hinj : Function.Injective (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f)) {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f) Δ io) :
    ∃ io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io' ∧
      ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io' x w) := by
  classical
  have hk : ∀ τ, ∃ k ∈ Formalism.REAL.Kset (M.ε τ), B τ = onb M τ * k := fun τ => by
    obtain ⟨k, hk, -, k2, -⟩ := exists_kset (M.fr_unit τ) (M.fr_gram τ) (hO τ) (hB τ)
    refine ⟨k, hk, k2.trans ?_⟩
    unfold onb
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.mul_one]
  choose k hk hBk using hk
  obtain ⟨s, hs⟩ : ∃ s : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ P,
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f P =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (s P) := by
    obtain rfl : B = fun τ => onb M τ * k τ := funext hBk
    have h := GlobalTheory.FockSubst.pureTensorO_subst D ψ θ V W S M BV f k
      (fun τ b a => if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) hω.std hθ hV hf hk fun _ _ _ => rfl
    generalize MvPolynomial.aeval (R := ℂ) (S₁ := MvPolynomial (FVar D W.rank V.rank) ℂ) _ = s at h
    exact ⟨s.toLinearMap, h⟩
  have e0 : ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io.compr₂ s x w) =
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun x w => (hs _).symm
  refine ⟨io.compr₂ s, ⟨fun u hu x w => by rw [e0, e0, hio.1 u hu],
    fun τ k hk v u hu w => by rw [e0, e0, hio.2.1 τ k hk v u hu], ?_⟩, fun x w => (e0 x w).symm⟩
  have t1 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict _ t1)
  have f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun _ _ => rfl
  clear_value F
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, l, n3, hl, e1⟩ := exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hO Δ n1 ((f1 _ w₀).trans (congrArg _ e))
  have l0 : l ≠ 0 := fun h => by simp [h] at hl
  refine ⟨v₁, l⁻¹ • w₀, n3, by rw [norm_smul, norm_inv, hl, n2, inv_one, one_mul], hinj ?_⟩
  rw [map_smul, map_smul, e0, ← f1, e1, smul_smul, inv_mul_cancel₀ l0, one_smul]

end GlobalTheory.GalOne.Rebase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum

variable (D : D7)

def cosetV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def congLev (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | k ∈ intG D N ∧ CongOne D 𝔪 k}

def blockLev (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : Subgroup (GA D d) :=
  Subgroup.closure {h | h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪}

variable {D}

def stdSum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ)
    (R : Finset (GA D a)) : VC D a d → ℂ :=
  ∑ r ∈ R, W.Om r 1 (cosetV D δ 𝔪 o a d e0)

theorem cosetVec_eq {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) :
    cosetVec P 𝔪 o = cosetV D δ 𝔪 o P.a P.d P.e0 := rfl

theorem congLev_le (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : congLev D 𝔪 N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem blockLev_le (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : blockLev D 𝔪 d a ≤ intG D d :=
  (Subgroup.closure_le _).2 fun _ h => h.1

example (N : ℕ) : blockLev D ⊤ N 0 = intG D N := by
  refine le_antisymm (blockLev_le _ _ _) fun h hh => Subgroup.subset_closure ⟨hh, fun i j hj _ => absurd hj (Nat.not_lt_zero _)⟩

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValuesIntegralStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_values_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), LocalUnits O → CubeValuesIntegral P := by
  first | exact @GlobalTheory.WeilIntegral.cubeValuesIntegral | exact GlobalTheory.WeilIntegral.cubeValuesIntegral | (intros; apply GlobalTheory.WeilIntegral.cubeValuesIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem iterated_decay : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  intro hfin E _ _ _ a N t ht i j hij m
  induction m with
  | zero =>
    intro ψ _ htame Ω hΩ
    obtain ⟨C0, hC0⟩ := htame []
    obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
    refine ⟨|C0| * B ^ N, by positivity, ?_⟩
    intro r d _ _ _ c hc
    have h1 := hC0 (d * c)
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h1
    have hh0 : 0 ≤ height (d * c) := le_trans zero_le_one (one_le_height _)
    have hh : height (d * c) ^ N ≤ (B * height d) ^ N := pow_le_pow_left₀ hh0 (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C0 * height (d * c) ^ N := h1
      _ ≤ |C0| * height (d * c) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh0 N)
      _ ≤ |C0| * (B * height d) ^ N := mul_le_mul_of_nonneg_left hh (abs_nonneg C0)
      _ = |C0| * B ^ N * (r j / r i) ^ 0 * height d ^ N := by rw [mul_pow]; ring
  | succ m ih =>
    intro ψ hψ htame Ω hΩ
    obtain ⟨Ω', B, C, hΩ', hC, hstep⟩ := GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step E a ψ hψ t ht i j hij Ω hΩ
    have hY : ∀ Y ∈ B, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
        ∀ c ∈ Ω', ‖(lie E a Y ψ).1 (infGL E a (d * c))‖ ≤ C' * (r j / r i) ^ m * height d ^ N := by
      intro Y _
      have hcusp : IsCuspForm (lie E a Y ψ) := GlobalTheory.T.isCuspForm_operator_act hfin E a (.lie Y) ψ hψ
      refine ih (lie E a Y ψ) hcusp ?_ Ω' hΩ'
      intro l
      obtain ⟨C1, hC1⟩ := htame (l ++ [Y])
      refine ⟨C1, fun y => ?_⟩
      have e : (l.map (lie E a)).prod (lie E a Y ψ) = ((l ++ [Y]).map (lie E a)).prod ψ := by
        simp [List.map_append, List.prod_append, Module.End.mul_apply]
      rw [e]
      exact hC1 y
    choose! CY hCY0 hCY using hY
    refine ⟨C * ∑ Y ∈ B, CY Y, mul_nonneg hC (Finset.sum_nonneg hCY0), ?_⟩
    intro r d hr hrt hd c hc
    have hq : 0 ≤ (r j / r i) ^ m * height d ^ N :=
      mul_nonneg (pow_nonneg (div_nonneg (hr j).le (hr i).le) m)
        (pow_nonneg (le_trans zero_le_one (one_le_height d)) N)
    have hM0 : 0 ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
      mul_nonneg (Finset.sum_nonneg hCY0) hq
    have h := hstep r d hr hrt hd _ hM0 (fun Y hYB c' hc' => by
      have h2 : lieD Y ψ.1 = (lie E a Y ψ).1 := rfl
      rw [h2]
      calc ‖(lie E a Y ψ).1 (infGL E a (d * c'))‖ ≤ CY Y * (r j / r i) ^ m * height d ^ N := hCY Y hYB r d hr hrt hd c' hc'
        _ = CY Y * ((r j / r i) ^ m * height d ^ N) := by ring
        _ ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun Y hY => hCY0 Y hY) hYB) hq) c hc
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * ((∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N)) := h
      _ = (C * ∑ Y ∈ B, CY Y) * (r j / r i) ^ (m + 1) * height d ^ N := by ring

end GlobalTheory.CuspRapid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchrodingerCompatibility
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.GenRep

theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (φ₁ φ₂ : (κ → R) → ℂ) :
    d.rho ψ w (φ₁ + φ₂) = d.rho ψ w φ₁ + d.rho ψ w φ₂ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (c : ℂ) (φ : (κ → R) → ℂ) :
    d.rho ψ w (c • φ) = c • d.rho ψ w φ := by
  funext x; simp [Darboux.rho, schr]; ring

theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) :
    d.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]

open scoped Classical in

theorem genRep : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsBy τ C ω₀ Φ (fockAct2 P Q R S) c₀ := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := GlobalTheory.T.theta_lift_darboux_adelic_symplectic hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add, map_add, hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    simp only [hω, hL]
    exact hder γ hγ Y hY T L

end GlobalTheory.GenRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumMorphismMatrixCompat
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SandwichRigid

section Abstract

variable {A : Type} [CommRing A] [IsDomain A]

theorem cancel_smul {m n : ℕ} {a : A} (ha : a ≠ 0) {X Y : Matrix (Fin m) (Fin n) A}
    (hXY : a • X = a • Y) : X = Y := by
  ext i j
  have := congrFun (congrFun hXY i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ ha this

theorem cancel_right {m n : ℕ} {F : Matrix (Fin n) (Fin n) A} (hF : F.det ≠ 0)
    {X Y : Matrix (Fin m) (Fin n) A} (hXY : X * F = Y * F) : X = Y := by
  apply cancel_smul hF
  have := congrArg (· * F.adjugate) hXY
  simpa only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] using this

theorem det_ne_zero_of_mul {n : ℕ} {a : A} (ha : a ≠ 0) {F G : Matrix (Fin n) (Fin n) A}
    (h : G * F = a • (1 : Matrix (Fin n) (Fin n) A)) : F.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem mul_comm_smul_one {n : ℕ} {a : A} (ha : a ≠ 0) {F G : Matrix (Fin n) (Fin n) A}
    (h : G * F = a • (1 : Matrix (Fin n) (Fin n) A)) :
    F * G = a • (1 : Matrix (Fin n) (Fin n) A) := by
  apply cancel_right (det_ne_zero_of_mul ha h)
  rw [Matrix.mul_assoc, h]
  simp

end Abstract

section Witt

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem G_eq [IsDomain (Ainf p O)] {ε : PreTilt O p} (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0)
    {h : ℕ} {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ] (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply cancel_right (det_ne_zero_of_mul hμ D.G_mul_F)
  have h1 : D.Ψ' * D.Ψ = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    mul_comm_smul_one hξ D.Ψ_mul
  have h2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  have h3 : D.G.map (phiInv p O) * D.F.map (phiInv p O)
      = nu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    rw [← Matrix.map_mul, D.G_mul_F, ← phiInv_mu]
    ext1 i j
    by_cases hij : i = j <;> simp [hij]
  rw [Matrix.mul_assoc, h2, Matrix.mul_smul, h3, smul_smul, xi_mul_nu, D.G_mul_F]

end Witt

end GlobalTheory.SandwichRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTargetStatement
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_loc_repr_contDiffOn_target : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | exact GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | (intros; apply GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityGlueingUnderTransitionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  first | exact @GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | exact GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | (intros; apply GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometricStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_shortExact_iso_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S S' : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂), e₁.hom ≫ S'.f = S.f ≫ e₂.hom → h.IsIsometry h' e₂ → (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧ h.bcInt hS h₁ h₃ = h'.bcInt hS' h₁' h₃' := by
  first | exact @GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | exact GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | (intros; apply GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso <;> assumption)
end

