import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0761
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimesLargeOfSizesUsed
section
noncomputable section

namespace GlobalTheory.DGamPrimeToLevel

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm

theorem minkMult_minkM (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) (n : ℕ) : MinkMult n (minkM n) := by
  intro H hH
  let e : Matrix.GeneralLinearGroup (Fin n) ℚ ≃* ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ (Fin n → ℚ))
  let G : Subgroup ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) := H.map e.toMonoidHom
  have e' : H ≃* G := e.subgroupMap H
  have hG : Finite G := Finite.of_equiv _ e'.toEquiv
  let v : G × Fin n → (Fin n → ℚ) := fun p => p.1.1 (Pi.basisFun ℚ (Fin n) p.2)
  let Λ : Submodule (𝓞 ℚ) (Fin n → ℚ) := Submodule.span (𝓞 ℚ) (Set.range v)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_range v)
  have hsp : Submodule.span ℚ (Λ : Set (Fin n → ℚ)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), rfl⟩
  have hst : ∀ g ∈ G, ∀ x ∈ Λ, g x ∈ Λ := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨g, hg⟩ * h, i), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul ℚ a x, map_smul, algebraMap_smul]
      exact Λ.smul_mem a hx
  have h := GlobalTheory.AutLattice.card_dvd_minkM hM ℚ (Fin n → ℚ) Λ hfg hsp G hG hst
  rw [Nat.card_congr e'.toEquiv]
  simpa using h

def PrimesLarge (D : D7) : Prop :=
  (∀ u, minkRank D + 1 < (D.mem u).A.T) ∧ (∀ a, minkRank D + 1 < D.host.g a) ∧
    minkRank D + 1 < D.host.q ∧ minkRank D + 1 < D.host.d

theorem primeToLevel_of_dvd {D : D7} (h : PrimesLarge D) {n : ℕ} (hn : n ∣ minkM (minkRank D)) :
    PrimeToLevel D n := by
  have hp : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ minkRank D + 1 := fun p hp hpn =>
    GlobalTheory.prime_le_succ_of_dvd_minkM _ p hp (hpn.trans hn)
  have key : ∀ p : ℕ, p.Prime → minkRank D + 1 < p → Nat.Coprime n p := by
    intro p hpp hlt
    refine ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => ?_).symm
    have := hp p hpp h
    omega
  obtain ⟨g1, g2, g3, g4⟩ := h
  exact ⟨hn, hp, key _ D.host.hyp.1 g3, key _ D.host.hyp.2.1 g4,
    fun a => key _ (D.host.g_prime a) (g2 a), fun u => key _ (D.mem u).A.T_prime (g1 u)⟩

theorem minkRank_le {D : D7} (L : SizeData₂ D) (hN : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (L.Ct + 1))
    (hx : 2 ≤ L.sc.x) : ((minkRank D + 1 : ℕ) : ℝ) ≤ L.sc.x ^ (2 * L.Ct + 5) := by
  have hf : D.R.f ≤ D.R.N D.R.m := le_trans (show D.R.f ≤ D.R.k from D.R.f_le_k) (Nat.le_add_right _ _)
  have h1 : 1 ≤ D.R.N D.R.m := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  have hf' : (D.R.f : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hf
  have h1' : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h1
  have hx0 : 0 < L.sc.x := by linarith
  have e : L.sc.x ^ (2 * L.Ct + 5) = (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have h8 : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
  have h2 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 := by gcongr
  have h3 : (D.R.N D.R.m : ℝ) ^ 2 * 2 ^ 3 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by gcongr
  rw [e]
  unfold minkRank
  push_cast
  nlinarith

theorem primesLarge_of_sizesUsed {D : D7} (L : SizeData₂ D) (h : SizesUsed L) : PrimesLarge D := by
  obtain ⟨⟨P⟩, hN, hT, hx⟩ := h
  have h0 := minkRank_le L hN hx
  have hq : minkRank D + 1 < D.host.q := by exact_mod_cast h0.trans_lt P.qd_pow.1
  have hd : minkRank D + 1 < D.host.d := by exact_mod_cast h0.trans_lt P.qd_pow.2
  have hC : SizeCond L := by
    have := P.condE_le
    unfold SizeCond szCond
    rw [Real.sqrt_eq_rpow]
    unfold LevelStarExponents.condE at this
    push_cast at this
    exact this
  have hs := GlobalTheory.DGamCoprime.q_le_sqrt_b L hC (by omega) (by omega)
  have hb := GlobalTheory.DGamCoprime.one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq, hd⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hY.trans (hg a).1)))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

theorem primeToLevelAt_of (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) {D : D7} (h : PrimesLarge D) (hD : DGamDef D)
    (hC : DGamChoice_at D) : PrimeToLevelAt D := by
  intro u μ
  rw [hD.one u u μ]
  exact primeToLevel_of_dvd h (hC _ (minkMult_minkM hM _) u)

theorem primesLarge_family {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧ ∀ i : Fm.Ix x, PrimesLarge (Fm.D x i) := by
  obtain ⟨x0, hT⟩ := hT
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ?_⟩
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  exact ⟨hx1, fun i => GlobalTheory.DGamCoprime.primes_gt (Fm.L x i) (Fm.sizes x hx1 i)
    (hT x ((le_max_left _ _).trans hx) i).1⟩

theorem row_of_minkowski (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : Row := by
  refine ⟨fun D L hS hD hC => primeToLevelAt_of hM (primesLarge_of_sizesUsed L hS) hD hC,
    fun eps Fm hC hT => ?_⟩
  obtain ⟨x0, hP⟩ := primesLarge_family Fm hT
  obtain ⟨x0', hC⟩ := hC
  refine ⟨max x0 x0', fun x hx i => ?_⟩
  obtain ⟨hx1, hP⟩ := hP x ((le_max_left _ _).trans hx)
  exact primeToLevelAt_of hM (hP i) (Fm.ex x hx1 i).err.dgam (hC x ((le_max_right _ _).trans hx) i)

theorem row : Row := row_of_minkowski GlobalTheory.MinkowskiExact.minkowskiBound

end GlobalTheory.DGamPrimeToLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjectiveStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.push_mem_liftFil_of_injective_alt : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  first | exact @GlobalTheory.SqLift.push_mem_liftFil_of_injective | exact GlobalTheory.SqLift.push_mem_liftFil_of_injective | (intros; apply GlobalTheory.SqLift.push_mem_liftFil_of_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReducesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLog_reduces_to_cocycle : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ f ∈ quasiLog p h, ∃ c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w) ∧ ∀ f ∈ quasiLog p h, ∀ c, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c → IsCoc μ c := by
  first | exact @GlobalTheory.quasiLog_reduces | exact GlobalTheory.quasiLog_reduces | (intros; apply GlobalTheory.quasiLog_reduces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadic
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.Conv

section SlopeTestRemainingChoices

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem exists_lim {p : ℕ} (h : IsFrame p E (RingHom.id O)) (a : ℕ → O) :
    ∃ L : O, ∀ N : ℕ, ∃ c : O,
      L = ∑ n ∈ Finset.range N, (p : O) ^ n * a n + (p : O) ^ N * c := by
  obtain ⟨L, hL⟩ := h.complete.toIsPrecomplete.prec
    (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]
      exact dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left
        (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))
  refine ⟨L, fun N => ?_⟩
  have hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L
      [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)] := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨-c, by linear_combination -hc⟩

theorem eq_zero_of_forall {p : ℕ} (h : IsFrame p E (RingHom.id O)) {x : E}
    (hx : ∀ N : ℕ, ∃ b : O, x = algebraMap O E ((p : O) ^ N * b)) : x = 0 := by
  obtain ⟨b, hb⟩ := hx 0
  have h0 : (p : O) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun N => by
    obtain ⟨c, hc⟩ := hx N
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [hb, h0, map_zero]

theorem comb_add_mul {ι : Type} [Fintype ι] (x y : ι → O) (c : O)
    (e : ι → MvPowerSeries (Fin d) E) :
    comb (fun i => x i + c * y i) e = comb x e + algebraMap O E c • comb y e := by
  unfold comb
  simp only [map_add, map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def IntD (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (g : MvPowerSeries (Fin d) E) : Prop :=
  (∀ i, ∃ b : O, lin g i = algebraMap O E b) ∧ In (⊤ : Ideal O) (cob1 (up E μ) g)

variable {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}

theorem up_const (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp [up, hμ]

theorem IntD.ofQL {g : MvPowerSeries (Fin d) E} (hg : QL μ ⊤ g) : IntD μ g :=
  ⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩

theorem IntD.zero (hμ : ∀ i, constantCoeff (μ i) = 0) : IntD μ (0 : MvPowerSeries (Fin d) E) := by
  have h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0 := by
    simpa using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)
  refine ⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩

theorem IntD.add (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g + g') := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    obtain ⟨b', hb'⟩ := hg'.1 i
    refine ⟨b + b', ?_⟩
    simp only [lin, map_add] at hb hb' ⊢
    rw [hb, hb']
  · obtain ⟨b, -, hb⟩ := hg.2 α
    obtain ⟨b', -, hb'⟩ := hg'.2 α
    exact ⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add, hb, hb', map_add]⟩

theorem IntD.smul (hμ : ∀ i, constantCoeff (μ i) = 0) (c : O) {g : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) : IntD μ (algebraMap O E c • g) := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    refine ⟨c * b, ?_⟩
    simp only [lin, coeff_smul] at hb ⊢
    rw [hb, map_mul]
  · obtain ⟨b, -, hb⟩ := hg.2 α
    exact ⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩

theorem IntD.sub (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g - g') := by
  have : g - g' = g + algebraMap O E (-1) • g' := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact hg.add hμ (hg'.smul hμ _)

theorem IntD.comb (hμ : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → O)
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, IntD μ (e i)) : IntD μ (comb b e) :=
  Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ)
    fun i _ => (he i).smul hμ (b i)

theorem IntD.map (hμ : ∀ i, constantCoeff (μ i) = 0) (s : MvPowerSeries (Fin d) O) :
    IntD μ (MvPowerSeries.map (algebraMap O E) s) := by
  refine ⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩
  have := ((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm
  rw [show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) =
      MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]
  exact In.top_iff.2 ⟨_, rfl⟩

end SlopeTestRemainingChoices

theorem generate_of_step : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  intro p _ O E _ _ _ h d μ hμ ι _ e he H f hf
  have hc := hμ.const
  choose! bf sf ff hQ hff using H
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n) :=
    ⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩
  have hFQ : ∀ n, QL μ ⊤ (F n) := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hf
    | succ n ih => rw [hFs]; exact hQ _ ih
  have step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1) :=
    fun n => by rw [hFs]; exact hff _ (hFQ n)
  have hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N) := fun N => by
    rw [map_pow, map_natCast]
  have tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
      ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N := by
    intro N
    induction N with
    | zero =>
      have : comb (fun _ : ι => (0 : O)) e = 0 := by simp [comb]
      simp only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [comb_add_mul, ← hpE]
      have hs := step N
      rw [ih] at *
      linear_combination (norm := module) ((p : E) ^ N) • hs
  choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)
  choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))
  obtain ⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α := ⟨Sc, fun _ => rfl⟩
  have key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧
      f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g := by
    intro N
    choose cB hcB using fun i => hB i N
    choose cS hcS using fun α => hS α N
    obtain ⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α := ⟨cS, fun _ => rfl⟩
    refine ⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩
    · exact ((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc
        (IntD.map hc T)
    · have h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
          (p : E) ^ N • comb cB e := by
        rw [hpE, ← comb_add_mul]
        congr 1
        funext i
        exact hcB i
      have h2 : map (algebraMap O E) S =
          ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) +
            (p : E) ^ N • map (algebraMap O E) T := by
        ext α
        rw [coeff_map, hSd, hcS α, map_add, map_add, coeff_smul, coeff_map, hTd, map_sum (coeff α)]
        simp only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]
      rw [h1, h2]
      linear_combination (norm := module) tele N
  have hR : f - comb Bv e - map (algebraMap O E) S = 0 := by
    refine GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E h d μ hμ _ ?_ ?_
    · funext i
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, hb⟩ := hg.1 i
      refine ⟨b, ?_⟩
      rw [hgN]
      simp only [lin, coeff_smul] at hb ⊢
      rw [hb, hpE, map_mul]
    · ext α
      rw [coeff_zero]
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, -, hb⟩ := hg.2 α
      refine ⟨b, ?_⟩
      rw [hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]
  exact ⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩

end GlobalTheory.QLog.Conv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPowStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (a b : MvPowerSeries (Fin d) F.B), QL μ' ⊤ f → QL μ' ⊤ g → In (⊤ : Ideal F.B) (frob p F.s f - g) → map (algebraMap F.B F.Q) a = defect μ' p f → map (algebraMap F.B F.Q) b = defect μ' p g → c.ev 1 (map F.θ b) - c.ev 1 (map F.θ a) ^ p ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) := by
  first | exact @GlobalTheory.QLog.defect_frob_pow | exact GlobalTheory.QLog.defect_frob_pow | (intros; apply GlobalTheory.QLog.defect_frob_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmulStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  first | exact @GlobalTheory.SemiPosLarge.semipos_add_smul | exact GlobalTheory.SemiPosLarge.semipos_add_smul | (intros; apply GlobalTheory.SemiPosLarge.semipos_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact GlobalTheory.T.obstructionClass_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := GlobalTheory.T.liftingObstructionBockstein_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacterStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) → subst c.μ u = inL u * inR u := by
  first | exact @GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | exact GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | (intros; apply GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfNoetherianCase
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_noetherian_case : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (exact GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (intros; apply GlobalTheory.EtC.gmPhi_surjective_of_noetherian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailSubstPAdicallySmallOfIntegralDifferentialStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_subst_pAdically_small_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  first | exact @GlobalTheory.tail_subst_small | exact GlobalTheory.tail_subst_small | (intros; apply GlobalTheory.tail_subst_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChainStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  first | exact @GlobalTheory.PeriodFamily.taylor_comp_chain | exact GlobalTheory.PeriodFamily.taylor_comp_chain | (intros; apply GlobalTheory.PeriodFamily.taylor_comp_chain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEvalStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  first | exact @GlobalTheory.PeriodFamily.taylor_coord_and_eval | exact GlobalTheory.PeriodFamily.taylor_coord_and_eval | (intros; apply GlobalTheory.PeriodFamily.taylor_coord_and_eval <;> assumption)
end

