import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetricStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V), ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) = cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  first | exact @GlobalTheory.Mem.Df.normAt_sq_eq_cSum | exact GlobalTheory.Mem.Df.normAt_sq_eq_cSum | (intros; apply GlobalTheory.Mem.Df.normAt_sq_eq_cSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)

set_option maxHeartbeats 800000 in

theorem thetaVector_eq_sum_translates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m), ∃ ε : ℤˣ, ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t), (∀ q, O.w t k q ≠ 0 → ∀ b, ∀ s ∈ (∏ PP ∈ R.Pg, PP.asIdeal) * ∏ PP ∈ R.Q (tup t), PP.asIdeal, s • q b = 0) ∧ ∀ N : ℕ, 0 < N → (O.dδ t).l₂.M ∣ N → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) N Y → R.vP i (tup t) = ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : ℕ) : ℂ)⁻¹ • ∑ᶠ q, inC O.c' (O.w t k q) • heisO R.ψ (Vc D i) (Wc D i) (finR (Vc D i) (rank_Wc i) (-(Y q))) (R.vacP i) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i
  by_cases hstd : VStd D i
  swap
  · exact ⟨1, fun Tp tup O hP => absurd hP.lift.std hstd⟩
  obtain ⟨hι, hiso⟩ := lat_iotaW T tie.laws i
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_second D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso
  refine ⟨-δ, fun Tp tup O hP t k => ?_⟩
  have hw : ∀ q, inC O.c' (O.w t k q) = GlobalTheory.AdTh.hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) q := fun q =>
    (congrArg (inC (O.dδ t).c₂) (hP.w t k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ t).c₂ _ q)
  have hφ : PhiIs R i (RingHom.id ℂ) (tup t) (iotaW T i) (Mfr (O.dδ t).l₂ • ⊤) fun x => inC O.c' (O.φ t x) :=
    (hP.tuple t).phi
  obtain ⟨h1, h2, h3⟩ := (hP.tuple t).half
  have hMb : (O.dδ t).l₂.Mb = T.Q.l.Mb * (O.dδ t).I := (hP.cov t).1.2.2.2.1
  have hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hQ : ∀ PP ∈ R.Q (tup t), (∏ PP ∈ R.Q (tup t), PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  refine ⟨fun q hq b s hs => ?_, fun N _ hN Y hY => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A _ R i _ _ _ _ _ _ hφ q
      (by rw [← hw]; exact (map_ne_zero _).2 hq) s
      (fun PP h => h.elim (fun h => hPg PP h (Ideal.mul_le_left hs)) fun h => hQ PP h (Ideal.mul_le_right hs)) b
    exact smul_eq_zero_of_smul_rep _ s z hz
  · have hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h =>
      ⟨by
        rw [hMb]
        exact h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h =>
          Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩
    have hY' := isRoots_sign (-δ) hN hY
    have hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1)) := by
      rw [← hι.2]
      exact latR_range _ _
    rw [← hL] at hY'
    have h := hδ (tup t) (O.dδ t).l₂ _ hφ hl 0 (O.dδ t).l₂.M 1 1 ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1))
      (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
      ⟨(O.dδ t).l₂.odd, dvd_rfl, le_inf Submodule.smul_le_right Submodule.smul_le_right⟩ ?_ _
      (fun q => ((-(Y q)).submatrix id (Fin.cast (rank_Wc i)))ᵀ) (fun q => finR (Vc D i) (rank_Wc i) (-(Y q))) hY' ?_
    · rw [show ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 from rfl, map_one, Module.End.one_apply,
        Module.End.one_apply] at h
      simp only [hw]
      exact h
    · intro v
      rw [show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]
      refine ⟨mem_std_star T.Q.H v, fun h => ?_⟩
      have h' := mem_std_star T.Q.H _ h
      simp only [star_star] at h'
      exact h'
    · intro a _
      refine ⟨0, zero_mem _, ?_⟩
      rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
      exact sub_self _
    · intro q
      refine ⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩
      rw [smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]

end GlobalTheory.OneMapRef.FinDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_complexForms_const_on_row_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' → pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) = pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  first | exact @GlobalTheory.Mem.Df.pairB_conj_cls_eq | exact GlobalTheory.Mem.Df.pairB_conj_cls_eq | (intros; apply GlobalTheory.Mem.Df.pairB_conj_cls_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartAtUpdSReFace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [hl σ hσ]
    exact h σ x hx

set_option maxHeartbeats 1000000 in

theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  have h := isKap_congr (lam' := (R.updS R.kap (zeroLam R F c)).lamN) hB
    fun μ j σ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  have h := fun i t => isLamP_congr (lam' := fun p => zeroLam R F c i t p A3.A.v0) (hA i t)
    fun σ hσ => scalarsZeroPartConvention_fixedPlace R F c hσ
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  have h := cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c) (fun j p v hv hp => zeroLam_off R F c hv hp) hG
  exact (by with_unfolding_all exact (h :))

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl

set_option maxHeartbeats 4000000 in

theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨fun i t p l hp hl => ?_, fun κ hk hne => ?_, fun i p v l hv hp he => ?_, fun i t p hp => ?_,
    fun i p v hv hp => ?_, fun i t p v hv => ?_⟩
  · exact (scalarsZeroPartConvention_fixedPlace R F _ hp).trans (hs.lam0 i t p l hp hl)
  · refine hs.kap κ (fun μ σ x hx => ?_) ?_
    · by_cases hσ : R.EEp3 σ = ⊥
      · rw [hσ, Submodule.mem_bot] at hx
        subst hx
        simp
      · have e := hk μ σ x hx
        rw [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hσ μ j] at e
        exact e
    · obtain ⟨t, p, hp, hne⟩ := hne
      exact ⟨t, p, hp, by rwa [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hp t j] at hne⟩
  · have hp' : R.PartAt F i p v := (partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).1 hp
    exact (zeroLam_off R F _ hv hp').trans (hs.off i p v l hv hp' he)
  · exact zeroLam_of_zero R F _ (Or.inl ⟨rfl, hp⟩)
  · exact zeroLam_of_zero R F _ (Or.inr ⟨hv, fun h => hp ((partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).2 h)⟩)
  · show zeroLam R F _ i t p v = zeroLam R F _ i A3.A.μ0 p v
    unfold zeroLam
    split_ifs with h
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

open Formalism.IndefR.Lev

open scoped Pointwise in

theorem not_isConjPl {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ Lev.IsConjPl w w' := by
  intro hc
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hz
  obtain ⟨v, hv, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv w
  have hv' := (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w v).1 hv
  have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
  subst hvw
  obtain ⟨ho, hiff⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w
    (P.overP hw)).2.2.2 (P.pb k) (P.pb_over k) v hv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k'
      · exact absurd rfl hne
      · exact D.host.g_ne
      · exact D.host.g_ne.symm
      · exact absurd rfl hne
    obtain ⟨s, t, hst⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hst]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ho) (v.asIdeal.mul_mem_left _ (P.overP hw'))
  subst hk
  exact hiff.1 hw hw'

theorem conv_of_idem {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra ℂ H) (hz : z * z = z) (g : H) :
    ∑ a, z.coeff a * z.coeff (a⁻¹ * g) = z.coeff g := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) :
    Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun X hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem postOn_gaL_mem (hθ : IsInfFam θ) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
    ext v h
    simp [gaL, postOn_apply]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L (eG g) X hX _ fun _ => rfl)

theorem gaL_gaL (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : gaL V β L eG c (gaL V β L eG c F) = gaL V β L eG c F := by
  letI : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F, gaL V β L eG c F = ∑ g, c (eG.symm g) • actG0 V β L g F := fun F => by
    unfold gaL
    rw [LinearMap.sum_apply]
    refine Fintype.sum_equiv eG.toEquiv _ _ fun g => ?_
    show c g • actG0 V β L (eG g) F = c (eG.symm (eG g)) • actG0 V β L (eG g) F
    rw [MulEquiv.symm_apply_apply]
  rw [e, e]
  refine GlobalTheory.FlagAction.convIdempotent_act V β L hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc]
  refine Fintype.sum_equiv eG.symm.toEquiv _ _ fun a => ?_
  show c (eG.symm a) * c (eG.symm (a⁻¹ * g)) = c (eG.symm a) * c ((eG.symm a)⁻¹ * eG.symm g)
  rw [map_mul, map_inv]

theorem postOn_gaL_mem_goodPart (hθ : IsInfFam θ) (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) (gaL V β L eG c) := by
  refine ⟨postOn_gaL_mem hθ eG c hX, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  ext1 v
  exact gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)

end Act

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem liftsExist_rows (h : R.toLevCh.Is A.μ0) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl R.C.P hk hk'

theorem eC_conv (hr : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h]
  rw [← conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  refine Fintype.sum_equiv eR.toEquiv _ _ fun a => ?_
  show _ = D.ntypes.e0.coeff (eR a) * D.ntypes.e0.coeff ((eR a)⁻¹ * eR g)
  rw [map_mul, map_inv]

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 :=
  (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x))).2

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    PiTensorProduct.lift.symm (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e0 := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv
    R.chi (R.xiR t)
  have e1 := e0.1
  have e2 := e0.2
  have h1 : R.thDn t x ∈ MultT R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) :=
    thDn_mem_CC R t x
  have h2 := (mem_multT R.θ (R.MY 0) _ _ _).1 h1
  have e1' : levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levG (Yc D 0) (R.βY 0) (R.dat0 R.triv) := e1
  have e2' : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := e2
  have h3 : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 R.triv), k ∈ levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) ∧
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := fun k hk => by
    have hk' : k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) := by rw [e1']; exact hk
    exact ⟨hk', e2' k hk'⟩
  exact mult_mono h3 h2

theorem proj_thDn_mem (h : R.toLevCh.Is A.μ0) (hθ : R.models_inf) (hr : R.grp_record) (t : T) (x : (R.HX t).H) :
    postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) ∈ R.EEat R.triv :=
  postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hθ (liftsExist_rows R h) R.eG _ (eC_conv R hr) (thDn_mem R t x)

end Real

theorem exists_chain_Th : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → ∃ Th, ({ R with Th := Th } : RealDat D A Ks).chain_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h _ hM hr
  have key : ∀ t, ∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H,
      ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) := fun t =>
    GlobalTheory.HilbertModel.exists_lift hM.HE
      (postOn (R.MY 0) R.e0 ∘ₗ
        (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t)
      (proj_thDn_mem R h hM.inf hr t)
  choose Th hTh using key
  exact ⟨Th, hTh⟩

end GlobalTheory.ProjectedLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContainedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_congruence_level_contained : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N' k → k ∈ principalLevelFrame.levN P N := by
  first | exact @GlobalTheory.LatCongImage.finCong_mem_levN | exact GlobalTheory.LatCongImage.finCong_mem_levN | (intros; apply GlobalTheory.LatCongImage.finCong_mem_levN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiGTrue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (I.rec7 l Z) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((I.rec7 l Z).host.g k : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F), Formalism.L2.Theta.IsPlaceIdem (I.rec7 l Z) v ε → ∀ c y : 𝓞 (I.rec7 l Z).host.F, Valued.v (algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (c : (I.rec7 l Z).host.F) - G.phi k v h (inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (I.rec7 l Z).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (I.rec7 l Z).host.F, (z : v.adicCompletion (I.rec7 l Z).host.F) = algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (I.rec7 l Z).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F) ((c : (I.rec7 l Z).host.F) * (y : (I.rec7 l Z).host.F) / ((I.rec7 l Z).host.g k : (I.rec7 l Z).host.F))) :=
  GlobalTheory.Mem.TypePrimes.Red.psiG_of_loc GlobalTheory.T.standardAddChar_placeIdempotent_div_prime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExtStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_closure_iso_ramified_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e → (∀ y, Valued.v (f y) = Valued.v y ^ e) → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → ∀ b₀ : Kbar v ≃+* Kbar v', (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x)) → ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔ IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  first | exact @GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | exact GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | (intros; apply GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map <;> assumption)
end

