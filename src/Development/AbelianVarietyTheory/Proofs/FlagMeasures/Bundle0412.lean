import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSq
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormCong

private theorem prime_dvd_int_of_cast_eq_mul {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O}
    (hq : Irreducible q) (hqℓ : q = (ℓ : O)) {m : ℤ} {c : O} (h : (m : O) = q * c) : (ℓ : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).2 hnd
  apply hq.not_isUnit
  have h1 : ((a * ℓ + b * m : ℤ) : O) = 1 := by rw [hab]; simp
  push_cast at h1
  rw [h, ← hqℓ] at h1
  exact isUnit_iff_exists_inv.2 ⟨a + b * c, by linear_combination h1⟩

theorem int_sq_dvd_of_eq {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O} (hq : Irreducible q)
    (hqℓ : q = (ℓ : O)) {n : ℤ} {c : O} (h : (n : O) = q ^ 2 * c) : (ℓ : ℤ) ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ (c := q * c) (by rw [h]; ring)
  push_cast at h
  rw [← hqℓ] at h
  have h2 : ((m : ℤ) : O) = q * c := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [h]; ring
  obtain ⟨k, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ h2
  exact ⟨k, by ring⟩

theorem exists_place_resChar (K : Type) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Formalism.MainNotions.S.Loc.resChar p = ℓ := by
  haveI hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) _ hker
  have hmem : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using h1
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((ℓ : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp h0)
  refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
  haveI := hQ
  show ringChar (𝓞 K ⧸ Q) = ℓ
  have hz : ((ℓ : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    simpa using hmem
  rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec _ ℓ).1 hz) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem sq_dvd_at (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hN : ∀ p, (FP p).NormsOK) (i : Fin 2) :
    ((D.host.g i : ℕ) : ℤ) ^ 2 ∣ (Tn : ℤ) - T'n := by
  obtain ⟨p, hp⟩ := exists_place_resChar D.host.F (D.host.g_prime i)
  have hsome : ((D.s.atP p).split).isSome := by
    rw [D.s_split p, hp]
    fin_cases i <;> simp
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rcases hg : (Z.M p).split with _ | g
  · rw [hg, hsg] at hm
    exact (hm : False).elim
  rw [hg, hsg] at hm
  obtain ⟨-, hq⟩ := hm
  obtain ⟨-, -, -, -, hG⟩ := hN p
  obtain ⟨-, c, hc⟩ := hG g hg
  obtain ⟨-, -, hA, hB'⟩ := hB p
  refine int_sq_dvd_of_eq (D.host.g_prime i) g.q_irr ?_ (c := c) ?_
  · apply Subtype.ext
    rw [hq, sg.q_eq, hp]
    simp
  · apply Subtype.ext
    push_cast
    rw [← hA, ← hB']
    exact hc

end GlobalTheory.NormCong

open GlobalTheory.NormCong in
theorem GlobalTheory.NormCong.norms_congr : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  intro D Z FP u u' F F' hB hN
  have h0 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 0
  have h1 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 1
  have hcop : IsCoprime (((D.host.g 0 : ℕ) : ℤ) ^ 2) (((D.host.g 1 : ℕ) : ℤ) ^ 2) := by
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have h := dvd_sub_comm.1 (hcop.mul_dvd h0 h1)
  rw [Nat.modEq_iff_dvd, show gS D = D.host.g 0 * D.host.g 1 from rfl]
  push_cast
  rw [mul_pow]
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UniChange

theorem sum_castLE {R : Type} [AddCommMonoid R] {l N : ℕ} (h : l ≤ N) (f : Fin N → R)
    (hf : ∀ c : Fin N, l ≤ c.val → f c = 0) :
    ∑ c, f c = ∑ i : Fin l, f (Fin.castLE h i) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro c hc
  apply hf
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, rfl⟩

theorem leadMinorE_mul_uni {K : Type} [Field K] {N : ℕ} (L Z A : Matrix (Fin N) (Fin N) K)
    (hL0 : ∀ a b : Fin N, a < b → L a b = 0) (hL1 : ∀ a : Fin N, L a a = 1)
    (hA0 : ∀ a b : Fin N, b < a → A a b = 0) (hA1 : ∀ a : Fin N, A a a = 1) (l : ℕ) :
    leadMinorE (L * Z * A) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · set e := Fin.castLE h with he
    have hsub : (L * Z * A).submatrix e e =
        L.submatrix e e * Z.submatrix e e * A.submatrix e e := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE h]
        intro c hc
        rw [hL0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), zero_mul]
      · intro d hd
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), mul_zero]
    have hLd : (L.submatrix e e).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hL1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hL0
        rw [Fin.lt_def]
        exact (show (i:ℕ) < j from OrderDual.toDual_lt_toDual.mp hij)
    have hAd : (A.submatrix e e).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hA1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hA0
        rw [Fin.lt_def]
        exact (show (j:ℕ) < i from hij)
    rw [hsub, Matrix.det_mul, Matrix.det_mul, hLd, hAd, one_mul, mul_one]
  · rfl

end GlobalTheory.UniChange

open GlobalTheory.UniChange in
theorem GlobalTheory.LocOver.gval_uni_change : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  intro D T T' F G F' G' A A' hA hA' hZ
  have key : ∀ l, leadMinorE (ZhatL G G') l = leadMinorE (ZhatL F F') l := by
    intro l
    rw [hZ]
    refine leadMinorE_mul_uni _ _ _ ?_ ?_ hA'.1 hA'.2 l
    · intro a b hab
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 b a hab]
    · intro a
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 a]
  have k1 := key (D.R.rS + 1)
  have k2 := key D.R.rS
  simp only [Gval, Gflag, Dl]
  simp only [ZhatL] at k1 k2
  rw [k1, k2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalLatticesCountEqProdLocalCountsBadPlaces
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Fibre

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem finrank_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp, rank_eq]

theorem theta_eq_one {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {p : PlF D}
    (h : (FP p).PrimeTo) : LocNG.theta (Z.M p) = 1 := by
  unfold LocNG.theta
  rw [h.1]

theorem isLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := GlobalTheory.T.localTermLattice_over_innerDatum_fg_span

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := GlobalTheory.T.localTerm_noDefect_primeTo_invariants

theorem fibre : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS y hrel hfin
  obtain ⟨hBased, hRelG, hPrime, hTerm0, Λ₀, hΛ₀, hΛ₀t⟩ := hB
  obtain ⟨-, -, -, -, hloc⟩ := hS
  have hLG := LatLoc.lattices_local_global D Z

  have single : ∀ p, p ∉ P → ∃! L, L ∈ locSet G G' p (y p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have key := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_eq p)
      (hRelG p) (hPrime p hp) A A' (fun a b h => ⟨hA.1 a b h, hA'.1 a b h⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
      (scaled Z p (frame G)) (scaled Z p (frame G'))
      (fun j => by rw [hc j, (hBased p).1]; rfl) (fun j => by rw [hc' j, (hBased p).2.1]; rfl)
      (d0 p) (hTerm0 p) (y p)
    exact key.1 (hrel p hp)

  have std : ∀ p, p ∉ P → y p = d0 p → lattice₂ D Z.M p Λ₀ ∈ locSet G G' p (y p) := by
    intro p hp hy
    rw [hy]
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have hT : LocNG.IsTermOver (FP p) (d0 p) (tm FP G G' p (lattice₂ D Z.M p Λ₀)) :=
      GlobalTheory.T.hermitian_frame_witness_integral_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_eq p) (hRelG p) (d0 p)
        (tm FP F F' p (lattice₂ D Z.M p Λ₀)) (hΛ₀t p hp) A A' (scaled Z p (frame G)) (scaled Z p (frame G')) hA hA'
        (fun a b => ⟨(hint a b).1, (hint a b).2, by
          rw [theta_eq_one (hPrime p hp), map_one]
          refine Submodule.mem_span_singleton.2 ⟨⟨A a b - A' a b, (Z.M p).L.O.sub_mem (hint a b).1 (hint a b).2⟩, ?_⟩
          first
            | (rw [Algebra.smul_def, mul_one]; rfl)
            | (rw [Submodule.smul_def]; simp)
            | (simp [Algebra.smul_def])
            | (erw [smul_eq_mul, mul_one])
            | (change (A a b - A' a b) * 1 = _; rw [mul_one])⟩) hc hc'
    exact ⟨hT, noDefect D Z FP p (hRelG p) (hPrime p hp) (d0 p) _ hT⟩

  let Φ : LV D → ∀ q : P, Submodule (Z.M q).L.O (Vp D q) := fun Λ q => lattice₂ D Z.M q Λ
  have hinj : Set.InjOn Φ (globSet G G' y) := by
    intro Λ₁ h₁ Λ₂ h₂ e
    refine (hLG.1 Λ₁ Λ₂ h₁.1 h₂.1).2 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun e ⟨p, hp⟩
    · exact (single p hp).unique (h₁.2 p) (h₂.2 p)
  have himg : Φ '' globSet G G' y = Set.univ.pi (fun q : P => locSet G G' q (y q)) := by
    ext g
    constructor
    · rintro ⟨Λ, hΛ, rfl⟩ q -
      exact hΛ.2 q
    · intro hg
      let Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p) := fun p =>
        if h : p ∈ P then g ⟨p, h⟩ else (single p h).exists.choose
      have hLp : ∀ p, Lp p ∈ locSet G G' p (y p) := by
        intro p
        by_cases h : p ∈ P
        · simp only [Lp, dif_pos h]; exact hg ⟨p, h⟩ (Set.mem_univ _)
        · simp only [Lp, dif_neg h]; exact (single p h).exists.choose_spec
      have hlat : ∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤ :=
        fun p => isLat D Z FP p (y p) (tm FP G G' p (Lp p)) (hLp p).1
      have hfin' : {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite := by
        refine ((P.finite_toSet).union hfin).subset fun p hp => ?_
        by_contra hn
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hn
        exact hp ((single p hn.1).unique (hLp p) (std p hn.1 hn.2))
      obtain ⟨Λ, hΛ, hΛp⟩ := hLG.2 Λ₀ hΛ₀ Lp hlat hfin'
      refine ⟨Λ, ⟨hΛ, fun p => by rw [hΛp p]; exact hLp p⟩, ?_⟩
      funext q
      show lattice₂ D Z.M q Λ = g q
      rw [hΛp q]
      show (if h : (q : PlF D) ∈ P then g ⟨q, h⟩ else (single q h).exists.choose) = g q
      rw [dif_pos q.2]
  have e1 := hinj.encard_image
  rw [himg, Set.encard_pi_eq_prod_encard] at e1
  rw [← e1]
  exact (map_prod ENat.toENNRealRingHom (fun i : P => (locSet G G' i (y i)).encard) Finset.univ).trans
    (Finset.prod_coe_sort P (fun p => ((locSet G G' p (y p)).encard : ℝ≥0∞)))

end GlobalTheory.GenMass.Fibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryFixingSpanPreservesGluedLattices
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueStable

theorem glueSet_gmap_mem : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  intro D U M g hg Λ hΛ
  obtain ⟨hgI, hgU⟩ := hg
  obtain ⟨hlat, huni, hcap⟩ := hΛ
  have H := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT g hgI Λ
  refine ⟨H.2.2.2.2.mpr hlat, H.2.2.2.1.mpr huni, ?_⟩
  rw [← hcap]
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e.symm ▸ h1, h2⟩

end GlobalTheory.GlueStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrian
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

open Formalism.MainNotions.S.Loc

section General

theorem linInd_of_change {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    {v w : ι → W} (B : Matrix ι ι R) (hB : IsUnit B.det) (hv : LinearIndependent R v)
    (hw : ∀ j, w j = ∑ i, B i j • v i) : LinearIndependent R w := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (B.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : B.mulVec g = 0 := funext (hv _ h1)
  have h3 : g = B⁻¹.mulVec (B.mulVec g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  intro i
  rw [h3, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem isUnit_ringInverse_of_ne {R : Type} [CommRing R] {y : R} (h : Ring.inverse y ≠ 0) :
    IsUnit (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact Units.isUnit _
  · exact absurd (Ring.inverse_non_unit y hy) h

theorem det_uni_eq_one {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Uni A) :
    A.det = 1 := by
  obtain ⟨hlow, hdiag⟩ := hA
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

end General

section Main

variable {D : D7}

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨P, hne, hP⟩ :=
    Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.host.F)
  exact ⟨⟨P, hP, hne⟩⟩

private theorem linearIndependent_frameD_of_T_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : LocNG.FrameD H r) (hT : Fr.T ≠ 0) : LinearIndependent E Fr.f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ y, H.h (∑ i, g i • Fr.f i) y = ∑ i, g i * H.h (Fr.f i) y := by
    intro y
    have hs : ∀ s : Finset (Fin (r + 1)),
        H.h (∑ i ∈ s, g i • Fr.f i) y = ∑ i ∈ s, g i * H.h (Fr.f i) y := by
      intro s
      refine Finset.induction_on s (by simp [H.h_zero_left]) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
    exact hs Finset.univ
  have hlast : g (Fin.last r) = 0 := by
    have hz := key (Fr.f (Fin.last r))
    rw [hg, H.h_zero_left, Fin.sum_univ_castSucc] at hz
    have hoff : ∀ i : Fin r, H.h (Fr.f i.castSucc) (Fr.f (Fin.last r)) = 0 :=
      fun i => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i))
    simp only [hoff, mul_zero, Finset.sum_const_zero, zero_add, Fr.h_zz] at hz
    have hu : IsUnit (-(algebraMap F E Fr.T)) := ((Ne.isUnit hT).map (algebraMap F E)).neg
    exact hu.mul_left_eq_zero.1 hz.symm
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have he := key (Fr.es j)
  rw [hg, H.h_zero_left, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simp only [Fr.h_es, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact he.symm

theorem local_pair_linInd (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS)
    (hR : P.RelG (LocNG.theta (Z.M p))) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim P.A.f P.B.f) := by
  obtain ⟨hX, -, -, -, -, -, hN⟩ := hR
  obtain ⟨-, hT, -, hT', -⟩ := hN
  exact LinearIndependent.sum_type (linearIndependent_frameD_of_T_ne_zero P.A hT) (linearIndependent_frameD_of_T_ne_zero P.B hT')
    (disjoint_iff.2 hX)

end Main

section Final

variable {D : D7}

theorem base_frames_linInd (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) :
    LinearIndependent D.host.E (Sum.elim (frame F) (frame F')) := by
  obtain ⟨p⟩ := exists_place D
  have hloc := local_pair_linInd Z p (FP p) (hR p)
  obtain ⟨hA, hA', -, -⟩ := hB p
  have hu : ∀ i, Sum.elim (FP p).A.f (FP p).B.f i =
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i • baseChange₂ D p (Sum.elim (frame F) (frame F') i) := by
    rintro (a | a)
    · simp only [Sum.elim_inl, hA]
    · simp only [Sum.elim_inr, hA']
  have hs : ∀ i, Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) *
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i = 1 := by
    intro i
    have hne : Sum.elim (frFac Z.δ p) (frFac Z.δ p) i ≠ 0 := by
      intro h0
      apply hloc.ne_zero i
      rw [hu i, h0, zero_smul]
    refine Ring.inverse_mul_cancel _ ?_
    rcases i with a | a
    · exact isUnit_ringInverse_of_ne hne
    · exact isUnit_ringInverse_of_ne hne
  rw [Fintype.linearIndependent_iff] at hloc ⊢
  intro g hg
  have h1 : ∑ i, ((D.s.atP p).ιE (g i) * Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i)) •
      Sum.elim (FP p).A.f (FP p).B.f i = 0 := by
    have hmap := congrArg (baseChange₂ D p) hg
    rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_smul, mul_assoc, hs i, mul_one, baseChange_smul₂]
  intro i
  have h2 := hloc _ h1 i
  have h3 : (D.s.atP p).ιE (g i) = 0 := by
    have h4 := congrArg (· * Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) h2
    simpa only [mul_assoc, hs i, mul_one, zero_mul] using h4
  exact (map_eq_zero_iff _ (D.s.atP p).ιE.injective).1 h3

theorem changed_frames_linInd : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  intro D Z FP Tn T'n F G F' G' hB hR hG hG'
  have hbase := base_frames_linInd Z FP Tn T'n F F' hB hR
  obtain ⟨A, hA, hcA⟩ := hG
  obtain ⟨A', hA', hcA'⟩ := hG'
  refine linInd_of_change (Matrix.fromBlocks A 0 0 A') ?_ hbase ?_
  · rw [Matrix.det_fromBlocks_zero₂₁, det_uni_eq_one hA, det_uni_eq_one hA', mul_one]
    exact isUnit_one
  · rintro (b | b)
    · simp only [Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      exact hcA b
    · simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      exact hcA' b

end Final
end GlobalTheory.GenMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSelfDualMeasuresFibreFamilyExistStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  first | exact @GlobalTheory.LocalFibre.dX_dT_omFam | exact GlobalTheory.LocalFibre.dX_dT_omFam | (intros; apply GlobalTheory.LocalFibre.dX_dT_omFam <;> assumption)
end

