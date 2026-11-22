import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TraceSemisimple

def spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) :
    Subalgebra K (Matrix (Fin a) (Fin a) K) :=
  (Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))).toSubalgebra
    (Submodule.subset_span ⟨1, by simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩)

theorem mem_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (x : Matrix (Fin a) (Fin a) K) :
    x ∈ spanAlg ρ ↔ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) := Iff.rfl

theorem isSemisimpleRing_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K)
    (h : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) :
    IsSemisimpleRing (spanAlg ρ) := by
  have : IsArtinianRing (spanAlg ρ) := IsArtinianRing.of_finite K _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply Subtype.ext
  refine h x.1 x.2 fun g => ?_
  let y : spanAlg ρ := ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩
  have hxy : x * y ∈ Ring.jacobson (spanAlg ρ) := Ideal.mul_mem_right _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson (spanAlg ρ)) := IsSemiprimaryRing.isNilpotent
  have h1 : (x * y) ^ n = 0 := by
    have := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    simpa using this
  have h2 : IsNilpotent ((x * y : spanAlg ρ) : Matrix (Fin a) (Fin a) K) :=
    ⟨n, by simpa using congrArg Subtype.val h1⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero

theorem isSSRep_of_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) →
    IsSSRep ρ := by
  intro Γ K _ _ a ρ h W hW
  have := isSemisimpleRing_spanAlg ρ h
  let f : spanAlg ρ →+* Module.End K (Fin a → K) :=
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin a)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  let : Module (spanAlg ρ) (Fin a → K) := Module.compHom _ f
  have hW' : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      ∀ v ∈ W, x.mulVec v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  let U : Submodule (spanAlg ρ) (Fin a → K) :=
    { toAddSubmonoid := W.toAddSubmonoid
      smul_mem' := fun x v hv => hW' x.1 x.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  let W' : Submodule K (Fin a → K) :=
    { toAddSubmonoid := U'.toAddSubmonoid
      smul_mem' := fun c v hv => by
        have : (c • (1 : Matrix (Fin a) (Fin a) K)).mulVec v ∈ U' :=
          U'.smul_mem ⟨c • 1, (spanAlg ρ).smul_mem (spanAlg ρ).one_mem c⟩ hv
        rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this }
  refine ⟨W', fun g v hv => ?_, ?_, ?_⟩
  · exact U'.smul_mem ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩ hv
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.1 hU.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hx hy

end GlobalTheory.TraceSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

open NumberField IsDedekindDomain in
open Polynomial Matrix in
private theorem eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero {K : Type} [Field K] [CharZero K]
    {a : ℕ} (B : Subalgebra K (Matrix (Fin a) (Fin a) K)) {z : Matrix (Fin a) (Fin a) K}
    (hzB : z ∈ B) (htr : ∀ y ∈ B, (z * y).trace = 0) {v : Fin a → K} (hv : z *ᵥ v = v) :
    v = 0 := by
  classical
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd z.charpoly
    (Matrix.charpoly_monic z).ne_zero 0
  set m := z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hpq hq
  have hc : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  set c := q.coeff 0 with hcdef
  set R := aeval z q.divX with hR
  have hq' : aeval z q = z * R + c • 1 := by
    calc aeval z q = aeval z (X * q.divX + C (q.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
      _ = z * R + c • 1 := by
        rw [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h0 : z ^ m * (z * R + c • 1) = 0 := by
    have := Matrix.aeval_self_charpoly z
    rwa [hpq, map_mul, map_pow, aeval_X, hq'] at this
  have hRz : z * R = R * z := by
    have := congrArg (aeval z) (mul_comm X q.divX)
    simpa [R] using this
  have h1 : z ^ (m + 1) * R = -(c • z ^ m) := by
    rw [pow_succ, mul_assoc]
    rw [mul_add, mul_smul_comm, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : z ^ m = z ^ (m + 1) * ((-c⁻¹) • R) := by
    rw [mul_smul_comm, h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, one_smul,
      neg_neg]
  set u := (-c⁻¹) • R with hu
  have hcomm : Commute z u := (show Commute z R from hRz).smul_right _
  have hstep : ∀ i, z ^ (m + i) = z ^ (m + i + 1) * u := by
    intro i
    rw [pow_add z m i, hkey, mul_assoc, ← (hcomm.pow_left i).eq, ← mul_assoc, ← pow_add,
      show m + 1 + i = m + i + 1 by omega]
  have hpow : ∀ k, z ^ (m + 1) = z ^ (m + 1 + k) * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, show m + 1 + k = m + (k + 1) by omega, hstep (k + 1), mul_assoc, ← pow_succ',
        show m + (k + 1) + 1 = m + 1 + (k + 1) by omega]
  have hRB : R ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hzB) (Polynomial.aeval_mem_adjoin_singleton K z)
  have huB : u ∈ B := B.smul_mem hRB _
  set n := m + 1 with hn
  have hnn := hpow n
  have hc' : u ^ n * z ^ n = z ^ n * u ^ n := (hcomm.pow_pow n n).eq.symm
  have he : IsIdempotentElem (z ^ n * u ^ n) := by
    show z ^ n * u ^ n * (z ^ n * u ^ n) = z ^ n * u ^ n
    rw [mul_assoc, ← mul_assoc (u ^ n) (z ^ n) (u ^ n), hc', ← mul_assoc, ← mul_assoc, ← pow_add,
      ← hnn]
  have hez : z ^ n * u ^ n * z ^ n = z ^ n := by
    rw [mul_assoc, hc', ← mul_assoc, ← pow_add, ← hnn]
  have htre : (z ^ n * u ^ n).trace = 0 := by
    have : z ^ n * u ^ n = z * (z ^ m * u ^ n) := by
      show z ^ (m + 1) * u ^ n = _
      rw [pow_succ', mul_assoc]
    rw [this]
    exact htr _ (B.mul_mem (B.pow_mem hzB m) (B.pow_mem huB n))
  have he0 : z ^ n * u ^ n = 0 := by
    have h1 : IsIdempotentElem (Matrix.toLin' (z ^ n * u ^ n)) := by
      unfold IsIdempotentElem at he ⊢
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    have h2 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h1).1
      (by rw [Matrix.trace_toLin'_eq, htre])
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hzn : z ^ n = 0 := by rw [← hez, he0, zero_mul]
  have hvn : ∀ k, (z ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  rw [← hvn n, hzn, Matrix.zero_mulVec]

open NumberField IsDedekindDomain in
open Polynomial Matrix in

theorem _root_.GlobalTheory.isSSRep_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), _root_.Formalism.MainNotions.N.IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K _ _ _ a ρ hss x hx htrx
  classical
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hss
  set P : Γ → Matrix (Fin a) (Fin a) K :=
    fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) with hP
  have hPmul : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [hP, map_mul]
  have hP1 : P 1 = 1 := by simp [hP]
  have hgen : ∀ g, P g ∈ Submodule.span K (Set.range P) := fun g => Submodule.subset_span ⟨g, rfl⟩
  have hleft : ∀ g, ∀ y ∈ Submodule.span K (Set.range P),
      P g * y ∈ Submodule.span K (Set.range P) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨h, rfl⟩ := hy; rw [← hPmul]; exact hgen _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hAmul : ∀ y ∈ Submodule.span K (Set.range P), ∀ w ∈ Submodule.span K (Set.range P),
      y * w ∈ Submodule.span K (Set.range P) := by
    intro y hy w hw
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hleft g w hw
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add y t _ _ hy ht => rw [add_mul]; exact Submodule.add_mem _ hy ht
    | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let B : Subalgebra K (Matrix (Fin a) (Fin a) K) :=
    { carrier := Submodule.span K (Set.range P)
      mul_mem' := fun hy hw => hAmul _ hy _ hw
      add_mem' := fun hy hw => Submodule.add_mem _ hy hw
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, ← hP1]
        exact Submodule.smul_mem _ c (hgen 1) }
  let J : Matrix (Fin a) (Fin a) K → Prop :=
    fun z => z ∈ Submodule.span K (Set.range P) ∧ ∀ g, (z * P g).trace = 0
  have hJtr : ∀ z, J z → ∀ y ∈ B, (z * y).trace = 0 := by
    intro z hz y hy
    have hy' : y ∈ Submodule.span K (Set.range P) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hg => obtain ⟨g, rfl⟩ := hg; exact hz.2 g
    | zero => simp
    | add y w _ _ h1 h2 => rw [mul_add, Matrix.trace_add, h1, h2, add_zero]
    | smul c y _ h => rw [mul_smul_comm, Matrix.trace_smul, h, smul_zero]
  have hJleft : ∀ g z, J z → J (P g * z) := by
    intro g z hz
    refine ⟨hleft g z hz.1, fun h => ?_⟩
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, ← hPmul]
    exact hz.2 _
  have hJright : ∀ g z, J z → J (z * P g) := by
    intro g z hz
    refine ⟨hAmul _ hz.1 _ (hgen g), fun h => ?_⟩
    rw [mul_assoc, ← hPmul]
    exact hz.2 _
  have hJ0 : J 0 := ⟨Submodule.zero_mem _, fun g => by simp⟩
  have hJadd : ∀ y z, J y → J z → J (y + z) := fun y z hy hz =>
    ⟨Submodule.add_mem _ hy.1 hz.1, fun g => by rw [add_mul, Matrix.trace_add, hy.2, hz.2, add_zero]⟩
  have hJsmul : ∀ (c : K) z, J z → J (c • z) := fun c z hz =>
    ⟨Submodule.smul_mem _ c hz.1, fun g => by rw [smul_mul_assoc, Matrix.trace_smul, hz.2, smul_zero]⟩
  have hfix : ∀ z, J z → ∀ v, z *ᵥ v = v → v = 0 := fun z hz v hv =>
    eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero B hz.1 (hJtr z hz) hv
  have hpres : ∀ S : Submodule K (Fin a → K), _root_.Formalism.MainNotions.N.IsInv ρ S →
      ∀ y ∈ Submodule.span K (Set.range P), ∀ s ∈ S, y *ᵥ s ∈ S := by
    intro S hS y hy s hs
    unfold _root_.Formalism.MainNotions.N.IsInv at hS
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hS g s hs
    | zero => rw [Matrix.zero_mulVec]; exact S.zero_mem
    | add y w _ _ h1 h2 => rw [Matrix.add_mulVec]; exact S.add_mem h1 h2
    | smul c y _ h => rw [Matrix.smul_mulVec]; exact S.smul_mem c h
  let W : Submodule K (Fin a → K) :=
    { carrier := {v | ∀ z, J z → z *ᵥ v = 0}
      add_mem' := fun {v w} hv hw z hz => by rw [Matrix.mulVec_add, hv z hz, hw z hz, add_zero]
      zero_mem' := fun z _ => Matrix.mulVec_zero z
      smul_mem' := fun c v hv z hz => by rw [Matrix.mulVec_smul, hv z hz, smul_zero] }
  have hWst : _root_.Formalism.MainNotions.N.IsInv ρ W := by
    unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    have hv' : ∀ z, J z → z *ᵥ v = 0 := hv
    show ∀ z, J z → z *ᵥ (P g *ᵥ v) = 0
    intro z hz
    rw [Matrix.mulVec_mulVec]
    exact hv' _ (hJright g z hz)
  obtain ⟨W', hW'st, hcompl⟩ := hss W hWst
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨S, ⟨hSst, hSW', hSne⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {S : Submodule K (Fin a → K) | _root_.Formalism.MainNotions.N.IsInv ρ S ∧ S ≤ W' ∧ S ≠ ⊥} ⟨W', hW'st, le_rfl, hne⟩
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
    let T : Submodule K (Fin a → K) :=
      { carrier := {w | ∃ z, J z ∧ z *ᵥ s = w}
        add_mem' := by
          rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, hJadd y z hy hz, Matrix.add_mulVec _ _ _⟩
        zero_mem' := ⟨0, hJ0, Matrix.zero_mulVec _⟩
        smul_mem' := by
          rintro c _ ⟨z, hz, rfl⟩
          exact ⟨c • z, hJsmul c z hz, Matrix.smul_mulVec _ _ _⟩ }
    have hTS : T ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact hpres S hSst z hz.1 s hsS
    have hTst : _root_.Formalism.MainNotions.N.IsInv ρ T := by
      unfold _root_.Formalism.MainNotions.N.IsInv
      rintro g _ ⟨z, hz, rfl⟩
      exact ⟨P g * z, hJleft g z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩
    by_cases hT : T = ⊥
    · apply hs0
      have hsW : s ∈ W := by
        show ∀ z, J z → z *ᵥ s = 0
        intro z hz
        have hzT : z *ᵥ s ∈ T := ⟨z, hz, rfl⟩
        rw [hT] at hzT
        exact (Submodule.mem_bot K).1 hzT
      exact (Submodule.disjoint_def.1 hcompl.disjoint) s hsW (hSW' hsS)
    · have hTeq : T = S := by
        by_contra hTS'
        exact hmin T ⟨hTst, hTS.trans hSW', hT⟩ (lt_of_le_of_ne hTS hTS')
      have hsT : s ∈ T := hTeq ▸ hsS
      obtain ⟨z, hz, hzs⟩ := hsT
      exact hs0 (hfix z hz s hzs)
  have hWtop : W = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hW'bot, sup_bot_eq] at h
  have hxJ : J x := ⟨hx, htrx⟩
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [Matrix.zero_mulVec]
  have hv : ∀ z, J z → z *ᵥ v = 0 := (hWtop ▸ Submodule.mem_top : v ∈ W)
  exact hv x hxJ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
end

