import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.GO.ChRoot

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_zero' : IntAt P (0 : E) := by simpa using intAt_natCast (P := P) 0

theorem intAt_one' : IntAt P (1 : E) := by simpa using intAt_natCast (P := P) 1

theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

variable [StarRing E]

theorem mem_stdAt' {n : ℕ} {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem mem_lamY_zero {q n c : ℕ} {x : Sp E (n + c)} : x ∈ LocE.lamY P q n c 0 ↔ x ∈ stdAt E (n + c) P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt', mem_stdAt']
  refine forall_congr' fun i => ?_
  simp [LocE.scE]

theorem eN_mem {N i : ℕ} : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt']
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one'
  · exact intAt_zero'

theorem intAt_n1Arg {n c : ℕ} (a : E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ x ∈ stdAt E (n + c) P, a • r x ∈ stdAt E (n + c) P) : IntAt P (a * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero'

omit [StarRing E] in

theorem unitV_root {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (h : LocE.unitV χ a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ LocE.unitV χ a ^ k = 1 := by
  unfold LocE.unitV at h ⊢
  split_ifs at h ⊢ with hu
  · have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact absurd rfl h

end Loc

theorem psi_root {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) (x : X.E)
    (hx : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x)) : c.psi P x ^ (qOf P.1 ^ c.D P) = 1 := by
  have key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k := by
    intro k
    induction k with
    | zero => simpa using hc.psi_int P 0 intAt_zero'
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]
      rw [mul_left_comm]
      exact (intAt_natCast k).mul hx
  rw [← key]
  exact hc.psi_int P _ (by simpa using hx)

theorem lam_root {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∉ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hb := hL.boundQ j b P' hP
  have hD := hL.depthQ' P' hP
  have hm := hL.hm
  simp only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb
  have hκ := hr.2
  simp only [Jat, hP, if_false] at hκ
  have hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1 := by
    intro x
    exact hκ.1 x
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r) := by
    refine intAt_n1Arg _ r fun x hx => ?_
    have h1 := (hb _ ((hκ' _).2 (hb x hx).1)).2
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rwa [← hh, h2] at h1
  have hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P' = d + j := ⟨cst.D P' - j, by omega⟩
    rw [hd, pow_add, mul_assoc, ← Nat.cast_pow]
    exact (intAt_natCast _).mul hint
  have h1 := psi_root hL.cst_ok P' _ hint'
  simp only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))
  refine ⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]
  simp

end GlobalTheory.GO.ChRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.TypePrimeUnif

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq {X : _root_.Formalism.L2.Col.Fields} (hX : X.Ok) {Pr : _root_.Formalism.L2.Col.Primes X}
    (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  refine ⟨hP.g_mem hv, fun hsq => ?_⟩
  have hdiv : ∀ Q ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ Q.asIdeal := fun Q hQ =>
    _root_.Formalism.L2.Col.decoFin_mem_of_mem_divs (show Q ∈ _root_.Formalism.L2.Col.divs (X.conjO (Pr.piG i)) from hQ)
  have hg1 : 1 < Pr.g i := (hP.g_prime i).one_lt
  have hN : Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)})
        = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, X.absNorm_nat, hX.rankQ]
    rw [X.absNorm_conjO, ← sq, pow_mul'] at h1
    rw [X.absNorm_conjO]
    exact Nat.pow_left_injective two_ne_zero h1
  have hπP : Pr.piG i ∉ P.asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ := hP.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a h) (P.asIdeal.mul_mem_left b (hdiv P hv))
  have hcop : IsCoprime (P.asIdeal ^ 2) (Ideal.span {Pr.piG i}) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := P.isMaximal.eq_of_le h le_sup_left
    exact hπP (by rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP2 : P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    have h : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, Ideal.dvd_span_singleton]
      exact hsq
    first
      | exact hcop.dvd_of_dvd_mul_left h
      | exact hcop.dvd_of_dvd_mul_right h
  let e : HeightOneSpectrum (𝓞 X.E) → ℕ := fun Q => if Q = P then 2 else 1
  have hall : ∏ Q ∈ Pr.vG i, Q.asIdeal ^ e Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q _ Q' _ hne
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro Q hQ
      by_cases h : Q = P
      · subst h
        simpa [e] using hP2
      · simpa [e, h, Ideal.dvd_span_singleton] using hdiv Q hQ
  have hnorm := map_dvd Ideal.absNorm hall
  rw [map_prod, hN] at hnorm
  have hcount : ∏ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ (X.f + 1) := by
    rw [Finset.prod_congr rfl (fun Q hQ => show Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ e Q by
      rw [map_pow, hP.vG_norm i Q hQ]), Finset.prod_pow_eq_pow_sum]
    congr 1
    have he : ∀ Q, e Q = 1 + if Q = P then 1 else 0 := fun Q => by
      by_cases h : Q = P <;> simp [e, h]
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', hv, if_true, hP.vG_card i]
  rw [hcount] at hnorm
  have := (Nat.pow_dvd_pow_iff_le_right hg1).mp hnorm
  omega

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (g : 𝓞 E)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) (a : E) (ha : _root_.Formalism.L2.Col.IntAt w a) (h0 : _root_.Formalism.L2.Col.redP w a = 0) :
    _root_.Formalism.L2.Col.IntAt w (a / algebraMap (𝓞 E) E g) := by
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have key : ∃ c r, ∃ s ∉ w.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk w.asIdeal s * c = Ideal.Quotient.mk w.asIdeal r := by
    obtain ⟨r, s, hs, hsr⟩ := ha
    have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact ⟨(Ideal.Quotient.mk w.asIdeal s)⁻¹ * Ideal.Quotient.mk w.asIdeal r, r, s, hs, hsr,
      mul_inv_cancel_left₀ hs0 _⟩
  unfold _root_.Formalism.L2.Col.redP at h0
  rw [dif_pos key] at h0
  have hspec := key.choose_spec
  rw [h0] at hspec
  obtain ⟨r, s, hs, hsr, hc⟩ := hspec
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton (I := w.asIdeal) (x := g)).mpr h1
  have hJw : ¬ J ≤ w.asIdeal := fun hle => h2 (by
    rw [sq]
    exact Ideal.mul_mono_right hle (hJ ▸ Ideal.mem_span_singleton_self g))
  obtain ⟨t, htJ, htw⟩ := Set.not_subset.mp hJw
  have hrt : r * t ∈ Ideal.span {g} := hJ ▸ Ideal.mul_mem_mul hc htJ
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hrt
  have hg0 : algebraMap (𝓞 E) E g ≠ 0 := by
    intro h
    apply h2
    rw [(IsFractionRing.injective (𝓞 E) E) (h.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨x, s * t, fun hst => (w.isPrime.mem_or_mem hst).elim hs htw, ?_⟩
  have hxE : algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g =
      algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, hx]
  have hmain : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a =
      algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g := by
    linear_combination algebraMap (𝓞 E) E t * hsr - hxE
  calc algebraMap (𝓞 E) E (s * t) * (a / algebraMap (𝓞 E) E g)
      = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a / algebraMap (𝓞 E) E g := by
        rw [map_mul]; ring
    _ = algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g / algebraMap (𝓞 E) E g := by rw [hmain]
    _ = algebraMap (𝓞 E) E x := mul_div_cancel_right₀ _ hg0

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_qOf : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X), X.Ok → Pr.Ok →
    ∀ w ∈ Pr.vGs, ∀ a : X.E, _root_.Formalism.L2.Col.IntAt w a →
    _root_.Formalism.L2.Col.redP w a = 0 → _root_.Formalism.L2.Col.IntAt w (a / (_root_.Formalism.L2.Col.qOf w : X.E)) := by
  classical
  intro X Pr hX hP w hw a ha h0
  have hw' : w ∈ Pr.vG 0 ∪ Pr.vG 1 := hw
  obtain ⟨i, hv⟩ : ∃ i, w ∈ Pr.vG i := by
    rcases Finset.mem_union.mp hw' with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hq : (_root_.Formalism.L2.Col.qOf w : X.E) = algebraMap (𝓞 X.E) X.E ((Pr.g i : ℕ) : 𝓞 X.E) := by
    unfold _root_.Formalism.L2.Col.qOf
    rw [map_natCast, hP.vG_norm i w hv]
  have hgw := _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hP i w hv
  rw [hq]
  exact _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq w _ hgw.1 hgw.2 a ha h0

end GlobalTheory.TypePrimeUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_eq_of_equiv_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] C)) (S' : Submodule LL (V' ⊗[Qp] C))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp C e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp C e.symm.toLinearMap x ∈ S) :
    finrank LL S = finrank LL S' := by
  have h1 : ∀ x : V ⊗[Qp] C, SumJumps.ext1 Qp C e.symm.toLinearMap
      (SumJumps.ext1 Qp C e.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  have h2 : ∀ x : V' ⊗[Qp] C, SumJumps.ext1 Qp C e.toLinearMap
      (SumJumps.ext1 Qp C e.symm.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear
    ((SumJumps.ext1 Qp C e.toLinearMap).restrict a)
    ((SumJumps.ext1 Qp C e.symm.toLinearMap).restrict b) ?_ ?_)
  · ext x
    simp [LinearMap.restrict_apply, h2]
  · ext x
    simp [LinearMap.restrict_apply, h1]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem symm_equivariant (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) (v : V') :
    e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) := by
  apply e.injective
  rw [he]
  simp

theorem finrank_dcris_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.dcris_map PD e.toLinearMap he)
    (SumJumps.dcris_map PD e.symm.toLinearMap (symm_equivariant e he))

theorem finrank_fildR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.fildR_map PD e.toLinearMap he τ a)
    (SumJumps.fildR_map PD e.symm.toLinearMap (symm_equivariant e he) τ a)

theorem multV_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  simp only [multV, finrank_fildR_eq_of_equiv PD e he]

theorem isCrys_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : IsCrys PD ρ') : IsCrys PD ρ := by
  unfold IsCrys at h ⊢
  rw [finrank_dcris_eq_of_equiv PD e he, h, e.finrank_eq]

end Transport

theorem isCrys_multV_of_isMatRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ}
    (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (h : IsMatRep T M) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧
      ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e (T.ρ g v) = matRep M g (e v) := by
    intro g v
    rw [he]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  exact ⟨isCrys_of_equiv _ e he', fun τ u => multV_eq_of_equiv _ e he' τ u⟩

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBounds
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

private theorem cast_succ_div_two_of_odd {t : ℕ} (ht : Odd t) :
    (((t + 1) / 2 : ℕ) : ℝ) = ((t : ℝ) + 1) / 2 := by
  obtain ⟨k, rfl⟩ := ht
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem _root_.GlobalTheory.HTW.wHat_le : ∀ {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (C : ℝ),
    _root_.GlobalTheory.HTW.Roomy L C →
    (_root_.GlobalTheory.HTW.wHat D : ℝ) = _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + _root_.GlobalTheory.HTW.sHat L + _root_.GlobalTheory.HTW.etaHat L + 1
      ≤ 2 * L.sc.b' := by
  intro D L C hL
  have hw : (_root_.GlobalTheory.HTW.wHat D : ℝ) =
      _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 := by
    unfold _root_.GlobalTheory.HTW.wHat
    push_cast [cast_succ_div_two_of_odd D.R.t_odd]
    rfl
  have hmax := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hL).1
  have hR := hL
  unfold _root_.GlobalTheory.HTW.Roomy at hR
  obtain ⟨-, -, h3, h4, -, -⟩ := hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hfS : (_root_.GlobalTheory.HTW.sHat L : ℝ) ≤ L.Sc := by
    unfold _root_.GlobalTheory.HTW.sHat
    exact Nat.floor_le hS.le
  have hfE : (_root_.GlobalTheory.HTW.etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold _root_.GlobalTheory.HTW.etaHat
    push_cast
    linarith [Nat.floor_le hE.le]
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]; nlinarith
  · rw [hw]; nlinarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem wB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ wB L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    positivity
  have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have h1 := L.etaSz_pos
  exact le_trans (by linarith) (le_max_left _ _)

theorem floor_size_le_wB {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hg : ¬ Thick D.host g) :
    ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) ≤ wB L := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρ' : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρ']; exact hg
  have key : wj D (j.1 + 1) ρ ≤ wB L := by
    by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
      have a := (L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2
      have b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ) :=
        le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩
      exact le_trans (by linarith) (le_max_right _ _)
    · have a := (L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2
      exact le_trans a (le_max_left _ _)
  rw [hw] at key
  have he : (hcAt D g).e j = (D.hc ρ).e j := rfl
  rw [he]
  rcases le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h
  · rw [show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h]
    have := Int.floor_le ((D.hc ρ).e j)
    have : (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    simpa using wB_nonneg L

theorem wMax_le_wB : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  intro D L
  have hB := wB_nonneg L
  have h1 : wMax D ≤ ⌊wB L⌋₊ := by
    apply csSup_le'
    rintro s ⟨g, j, hg, rfl⟩
    exact Nat.le_floor (floor_size_le_wB L g j hg)
  have h2 : (wMax D : ℝ) ≤ wB L :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le hB)
  refine ⟨h2, ?_⟩
  have h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)
    push_cast at this
    exact this
  unfold wHat wP
  push_cast
  linarith

end GlobalTheory.HTW.Rec
end
end

