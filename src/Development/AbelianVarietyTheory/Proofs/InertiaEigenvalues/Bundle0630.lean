import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalPot

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (d : ι → OA l O) :
    inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem isCrisVal_add {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') :
    IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, h1, h2⟩ := h
  obtain ⟨m', c', hm', h1', h2'⟩ := h'
  refine ⟨m * m', m' • c + m • c', by rw [map_mul]; exact hm.mul hm', ?_, ?_⟩
  · rw [map_add, inclL_smul, inclL_smul, ← h1, ← h1', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (inclO l O m) (inclO l O m') w]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    rw [e1, map_add, map_smul, map_smul, ← h2, ← h2', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (toB l O m) (toB l O m') b]

theorem isCrisVal_zero {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} : IsCrisVal t ϖ P jB 0 0 :=
  ⟨1, 0, by rw [map_one]; exact isUnit_one, by rw [smul_zero, map_zero], by
    rw [smul_zero]
    have e0 : (fun i => toB l O ((0 : ι → OA l O) i)) = 0 := funext fun i => map_zero (toB l O)
    rw [e0, map_zero]⟩

theorem isCrisVal_nsmul {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (n : ℕ) : IsCrisVal t ϖ P jB (n • w) (n • b) := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; exact isCrisVal_zero
  | succ n ih => rw [succ_nsmul, succ_nsmul]; exact isCrisVal_add ih h

variable [TameDescentExponentData K l e a] {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}

theorem isPotential_add (R : GalDat t ϖ s D T) {y y' : Vec K a ι} {b b' : TW (OB l O) T}
    (h : R.IsPotential y b) (h' : R.IsPotential y' b') : R.IsPotential (y + y') (b + b') := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨add_mem hy hy', m₀ + m₀', σ + σ', b₀ + b₀', ?_, add_mem h2 h2', ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (⟨y, hy⟩ + ⟨y', hy'⟩)
    rw [map_add, map_add, ← h1, ← h1']
    abel
  · rw [Submodule.coe_add, map_add, map_add, h3, h3']
  · rw [map_add]
    exact isCrisVal_add h4 h4'
  · rw [h5, h5', map_add, map_add]
    abel

theorem isPotential_nsmul (R : GalDat t ϖ s D T) {y : Vec K a ι} {b : TW (OB l O) T}
    (h : R.IsPotential y b) (n : ℕ) : R.IsPotential (n • y) (n • b) := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  refine ⟨(ME D.toPhiMod).nsmul_mem hy n, n • m₀, n • σ, n • b₀, ?_, D.desc.inv.nsmul_mem h2 n, ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (n • ⟨y, hy⟩)
    rw [map_nsmul, map_nsmul, ← h1, smul_sub]
  · show D.conn (n • σ.1) = _
    rw [map_nsmul, map_nsmul, h3]
  · rw [map_nsmul]
    exact isCrisVal_nsmul h4 n
  · rw [h5, map_nsmul, map_nsmul, nsmul_sub]

theorem isCobOf_pow {b : TW (OB l O) T} {c : G → T.V} (h : IsCobOf s T b c) (k : ℕ) :
    IsCobOf s T ((l ^ k : ℕ) • b) ((l : K) ^ k • c) := by
  intro g n x hx
  have h1 := h g (n + k) x (by rw [hx, Pi.smul_apply, smul_smul, pow_add])
  rw [h1, map_nsmul, ← nsmul_sub, ← Nat.cast_smul_eq_nsmul O, smul_smul, Nat.cast_pow, pow_add]

theorem exists_isEps : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
  exact ⟨ε, h1, (frobeniusEquiv (Per.Fl l) l).symm ε, frobeniusEquiv_symm_pow_p _ _ _, h2⟩

theorem isUnit_toB_muOf {ε : OCb l} (hε : IsEps ε) (n : ℕ) :
    IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hu : IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) :=
    ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε)) ^ n) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e1]
  exact (hu.pow n).map _

theorem actB_mul (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g g' : G) (z : TW (OB l O) T) :
    actB s T (g * g') z = actB s T g (actB s T g' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w x =>
    have hw : galOB O (s (g * g')) w = galOB O (s g) (galOB O (s g') w) := by
      rw [map_mul]
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul o c =>
        simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun z : Per.Bcris l => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ c)
    have hx : T.actT (g * g') x = T.actT g (T.actT g' x) :=
      Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g g') (x : T.V))
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hw, hx]

theorem sub_mem_B1T {s : G →* GQ l} {T : LocLat G ℚ_[l] K O} {b b' ξ : TW (OB l O) T} {c c' : G → T.V}
    (x : ↥T.L.T) (hb : IsCobOf s T b c) (hb' : IsCobOf s T b' c') (hξ : ∀ g, actB s T g ξ = ξ)
    (h : b - b' = ξ - (1 : OB l O) ⊗ₜ[O] x) : c - c' ∈ latticeCoboundaries T.L := by
  refine ⟨-(x : T.V), neg_mem x.2, funext fun g => ?_⟩
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c g)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c' g)
  obtain ⟨x₁, hx₁⟩ := hn₁ (max n₁ n₂) (le_max_left _ _)
  obtain ⟨x₂, hx₂⟩ := hn₂ (max n₁ n₂) (le_max_right _ _)
  have e1 := hb g _ x₁ hx₁
  have e2 := hb' g _ x₂ hx₂
  have hact : actB s T g ((1 : OB l O) ⊗ₜ[O] x) = (1 : OB l O) ⊗ₜ[O] (T.actT g x) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hbb : b = b' + (ξ - (1 : OB l O) ⊗ₜ[O] x) := by rw [← h]; abel
  have e3 : (1 : OB l O) ⊗ₜ[O] (x₁ - x₂) =
      (1 : OB l O) ⊗ₜ[O] (((l : O) ^ max n₁ n₂) • (x - T.actT g x)) := by
    rw [TensorProduct.tmul_sub, e1, e2, ← smul_sub, TensorProduct.tmul_smul, TensorProduct.tmul_sub, ← hact,
      hbb, map_add, map_sub, hξ]
    congr 1
    abel
  have e4 := congrArg (fun z : ↥T.L.T => (z : T.V)) (GlobalTheory.T.one_tmul_injective_locLat l O K G T e3)
  simp only [Submodule.coe_sub, Submodule.coe_smul] at e4
  have eO : ∀ v : T.V, ((l : O) ^ max n₁ n₂) • v = (l : K) ^ max n₁ n₂ • v := fun v => by
    rw [← algebraMap_smul K ((l : O) ^ max n₁ n₂) v, map_pow, map_natCast]
  rw [hx₁, hx₂, ← smul_sub, eO] at e4
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have e5 := (smul_right_inj (pow_ne_zero (max n₁ n₂) hl0)).1 e4
  simp only [LinearMap.restrictScalars_apply, Pi.sub_apply]
  rw [e5]
  change T.ρ g (-(x : T.V)) - (-(x : T.V)) = (x : T.V) - T.ρ g (x : T.V)
  rw [map_neg]
  abel

section Ql

variable [TameDescentExponentData K l e a] {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat (Gl l) ℚ_[l] K O}

theorem exists_isCrisVal (R : GalDat t ϖ (sQ l) D T) {y : Vec K a ι} (hyY : y ∈ D.Y) (hy : y ∈ ME D.toPhiMod)
    (m₀ : ι → OW l O) (h : phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩) :
    ∃ b₀, IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ := by
  obtain ⟨ε, hε⟩ := exists_isEps (l := l)
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨c, hc⟩ := (GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩
    hyY.1 m₀ h).2
  obtain ⟨u, hu⟩ := isUnit_toB_muOf (O := O) hε (H + η)
  refine ⟨(↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i)), (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)), c,
    ⟨u, hu⟩, hc.symm, ?_⟩
  rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem fix_of_horiz (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (hinv : σ.1 ∈ D.desc.inv)
    (hc : D.conn σ.1 = 0) (g : Gl l) :
    actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) := by
  obtain ⟨h, k, rfl, hh, γ, hk⟩ := GlobalTheory.T.exists_galois_decomp_tameCover_action l a e O K t ϖ g
  have hx := GlobalTheory.T.eq_xi_red_of_conn_eq_zero' O K l e a ι D.toPhiMod σ.1 hc
  have hm : D.xi (red σ.1) ∈ D.MMl := by rw [← hx]; exact σ.2
  have hσ : (⟨D.xi (red σ.1), hm⟩ : D.MMl) = σ := Subtype.ext hx.symm
  have h2 := R.horiz h hh (red σ.1) hm
  rw [hσ] at h2
  have h3 := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc k γ hk σ σ (hinv γ).symm
  rw [actB_mul, h3, h2]

end Ql

theorem potential_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hyY
    have hy : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hyY
    obtain ⟨m₀, hm₀⟩ := R.I.exists_phiW_sub (toW t ϖ D.toPhiMod ⟨y, hy⟩)
    have hYl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hyY⟩
    obtain ⟨⟨σ, hσ, hinv, hconn, -⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hYl
    obtain ⟨b₀, hb₀⟩ := exists_isCrisVal R hyY hy m₀ hm₀
    exact ⟨_, hy, m₀, ⟨σ, hσ⟩, b₀, hm₀, hinv, hconn, hb₀, rfl⟩
  · rintro y c c' ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩, hc⟩ ⟨b', ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩, hc'⟩
    have hT : m₀ - m₀' ∈ Treal t ϖ D.toPhiMod := by
      rw [mem_Treal, map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.1 (h1.trans h1'.symm)
    obtain ⟨x, hx⟩ : m₀ - m₀' ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hT
    have hphi : phiW t ϖ D.toPhiMod m₀' + R.I.ofT x = phiW t ϖ D.toPhiMod m₀ := by
      rw [hx, ← mem_Treal.1 hT, map_sub]
      abel
    have hof := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.2.2.1 x
    have hsum := isCrisVal_add h4' hof
    rw [hphi] at hsum
    have hb₀ : b₀ = b₀' + (1 : OB l O) ⊗ₜ[O] x := UnitModel.isCrisVal_unique t ϖ h4 hsum
    refine sub_mem_B1T x hc hc' (fix_of_horiz R (σ - σ') (sub_mem h2 h2') ?_) ?_
    · show D.conn (σ.1 - σ'.1) = 0
      rw [map_sub, h3, h3', sub_self]
    · rw [h5, h5', hb₀, map_sub, map_sub]
      abel
  · rintro y c k ⟨b, hb, hc⟩
    refine ⟨(l ^ k : ℕ) • b, ?_, isCobOf_pow hc k⟩
    have := isPotential_nsmul R hb (l ^ k)
    rwa [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow] at this
  · rintro y c m hm ⟨b, hb, hc⟩
    exact ⟨b + 0, isPotential_add R hb (UnitModel.isPotential_phi_sub t ϖ R hm), by rwa [add_zero]⟩

end GlobalTheory.GalPot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.exists_letter_vector_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  intro l _ P AI hT K LL x hx c hc μ τ₀' τ' j hμ hτ d hd hd1
  have := (P.PD K).finK₀
  obtain ⟨m, cc, kk, h1, hsum⟩ := GlobalTheory.exists_embedding_idempotent_tensor ℚ_[l] ↥(K0 K) ↥LL.1 τ'
  set y := (⇑P.φB)^[j] x with hy
  set z := P.ιB y with hzdef
  clear_value z y
  let f : ↥(K0 K) →ₗ[ℚ_[l]] P.R.B := (LinearMap.mulRight ℚ_[l] y) ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hB : ∀ s : ↥(K0 K), ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) = ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by
    intro s
    have := congrArg (LinearMap.lTensor ↥LL.1 f) (hsum s)
    simpa [f, map_sum, LinearMap.lTensor_tmul] using this
  have hφK : ∀ k : ↥(K0 K), P.φB (algebraMap ↥(K0 K) P.R.B k) = algebraMap ↥(K0 K) P.R.B ((P.PD K).σ k) := by
    intro k; rw [← P.PD_φ K]; exact (P.PD K).φ_K₀ k
  have hact : ∀ g : ↥(GK K), ∀ n : ℕ, P.actQ (g : GQ l) ((⇑P.φB)^[n] x) = algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[n] (c g : ↥(K0 K))) * (⇑P.φB)^[n] x := by
    intro g n
    have hcomm : ∀ b, P.actQ (g : GQ l) (P.φB b) = P.φB (P.actQ (g : GQ l) b) := by
      intro b
      have := (P.PD K).φ_comm g b
      rw [P.PD_φ, P.PD_φ, P.PD_actB, P.PD_actB] at this
      exact this.symm
    induction n with
    | zero => simpa using hc g
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [hcomm, ih, map_mul, hφK]
  have hterm : ∀ (g : ↥(GK K)) (a : ↥LL.1) (k : ↥(K0 K)),
      actVB (P.PD K) (charRep μ) g (a ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B k * y)) =
        (((μ g : (↥LL.1)ˣ) : ↥LL.1) * a) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[j] (c g : ↥(K0 K)) * k) * y) := by
    intro g a k
    simp only [actVB, AlgebraTensorModule.map_tmul]
    congr 1
    change (P.PD K).actB g (algebraMap ↥(K0 K) P.R.B k * y) = _
    rw [map_mul, AlgEquiv.commutes, P.PD_actB, hy, hact g j, map_mul]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ↥LL.1 ⊗[ℚ_[l]] P.R.B, w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := ⟨_, rfl⟩
  have hinv : ∀ g : ↥(GK K), actVB (P.PD K) (charRep μ) g w = w := by
    intro g
    set s := (⇑(P.PD K).σ)^[j] (c g : ↥(K0 K))
    simp only [hw, map_sum, hterm]
    calc ∑ i, (((μ g : (↥LL.1)ˣ) : ↥LL.1) * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y)
        = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) := by
          rw [Finset.smul_sum]; simp only [TensorProduct.smul_tmul', smul_eq_mul]
      _ = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by rw [hB]
      _ = _ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← mul_assoc, hτ, hμ, one_mul]

  have hlet : ∀ a : ↥(K0 K), mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := ↥LL.1) (LL := ↥LL.1) a w = τ' a • w := by
    intro a
    simp only [hw, map_sum, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    have : ∀ i, algebraMap ↥(K0 K) P.R.B a * (algebraMap ↥(K0 K) P.R.B (kk i) * y) = algebraMap ↥(K0 K) P.R.B (a * kk i) * y := by
      intro i; rw [map_mul, mul_assoc]
    simp only [this]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hι : ∀ k : ↥(K0 K), (P.PD K).ι (algebraMap ↥(K0 K) P.R.B k * y) = algebraMap ↥(K0 K) P.R.BdR k * z := by
    intro k; rw [map_mul, AlgHom.commutes, P.PD_ι, ← hzdef]
  have hιw : ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.BdR (kk i) * z) := by
    simp only [hw, map_sum, ιV, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact hι (kk i)
  have hmem : ∀ k : ↥(K0 K), algebraMap ↥(K0 K) P.R.BdR k * z ∈ (P.PD K).Fil d := by
    intro k
    rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, ← Algebra.smul_def]
    exact (P.PD K).Fil d |>.smul_mem _ hd
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Dcris
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hinv g, LinearMap.id_apply, sub_self]
  · refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hlet a, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
  · rw [hιw]
    refine ⟨∑ i, cc i ⊗ₜ[ℚ_[l]] (⟨algebraMap ↥(K0 K) P.R.BdR (kk i) * z, hmem (kk i)⟩ : ↥(((P.PD K).Fil d).restrictScalars ℚ_[l])), ?_⟩
    simp [map_sum, AlgebraTensorModule.map_tmul]
  · intro hcon
    have hyu : ∀ n : ℕ, IsUnit ((⇑P.φB)^[n] x) := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.map P.φB
    have hz : IsUnit z := by rw [hzdef, hy]; exact (hyu j).map P.ιB
    obtain ⟨v, hzv⟩ := hz.exists_right_inv
    have hvz : v * z = 1 := by rw [mul_comm]; exact hzv
    have hv : v ∈ (P.PD K).Fil (-d) := GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d z v hzv hd hd1
    let Mv : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] P.R.BdR :=
      AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) (LinearMap.mulLeft ℚ_[l] v)
    have hvmul : ∀ b ∈ ((P.PD K).Fil (d + 1)).restrictScalars ℚ_[l], LinearMap.mulLeft ℚ_[l] v b ∈ ((P.PD K).Fil 1).restrictScalars ℚ_[l] := by
      intro b hb
      have := (P.PD K).Fil_mul (-d) (d + 1) v b hv hb
      rw [show -d + (d + 1) = 1 by ring] at this
      exact this
    have hMv : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1), Mv t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1 := by
      rintro t ⟨s, rfl⟩
      refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) ((LinearMap.mulLeft ℚ_[l] v).restrict hvmul) s, ?_⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Mv, AlgebraTensorModule.map_tmul]
      | add s t hs ht => simp only [map_add, hs, ht]
    have hE : Mv (ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w) = ∑ i, cc i ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.BdR (kk i) := by
      rw [hιw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Mv, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [mul_left_comm, hvz, mul_one]
    have hF1 := hMv _ hcon
    rw [hE] at hF1
    let q := (((P.PD K).Fil 1).restrictScalars ℚ_[l]).mkQ
    let h0 : ↥(K0 K) →ₗ[ℚ_[l]] P.R.BdR ⧸ (((P.PD K).Fil 1).restrictScalars ℚ_[l]) :=
      q ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.BdR).toLinearMap
    have hinj : Function.Injective h0 := by
      rw [injective_iff_map_eq_zero]
      intro k hk
      have hk' : algebraMap ↥(K0 K) P.R.BdR k ∈ (P.PD K).Fil 1 := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hk
        exact this
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR] at hk'
      have := JsetEmb.field_inter_filtration_one_eq_zero (P.PD K) _ hk'
      exact (map_eq_zero_iff _ (algebraMap ↥(K0 K) ↥K.1).injective).1 this
    have hq : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1, LinearMap.lTensor ↥LL.1 q t = 0 := by
      rintro t ⟨s, rfl⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
        rw [show q ((((P.PD K).Fil 1).restrictScalars ℚ_[l]).subtype b) = 0 from (Submodule.Quotient.mk_eq_zero _).2 b.2, tmul_zero]
      | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]
    have hzero : LinearMap.lTensor ↥LL.1 h0 (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 0 := by
      have := hq _ hF1
      simpa [h0, map_sum, LinearMap.lTensor_tmul] using this
    have he : (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) h0 hinj (hzero.trans (map_zero _).symm)
    let Λ : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] ↥LL.1 := TensorProduct.lift ((LinearMap.mul ℚ_[l] ↥LL.1).compl₂ τ'.toLinearMap)
    have hΛ : Λ (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 1 := by
      simp [Λ, map_sum, h1]
    rw [he, map_zero] at hΛ
    exact zero_ne_one hΛ
end

