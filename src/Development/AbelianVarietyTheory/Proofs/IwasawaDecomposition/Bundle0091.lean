import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
import ReciprocityTheory.GaloisValuations.Global
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, phiA l C.t = (l : Per.Acris l) * C.t := by
  first | exact @GlobalTheory.MemLoc.TPhi.t_phi | exact GlobalTheory.MemLoc.TPhi.t_phi | (intros; apply GlobalTheory.MemLoc.TPhi.t_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l), sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  first | exact @GlobalTheory.MemLoc.TAct.t_act | exact GlobalTheory.MemLoc.TAct.t_act | (intros; apply GlobalTheory.MemLoc.TAct.t_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfKernelPowerClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem image_kerP_pow_separated : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.Ainf l), (∀ k : ℕ, ∃ b : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) (a - ((l : ℕ) : Per.Ainf l) ^ k * b) ∈ Per.kerP l ^ n) → algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  intro l _ n a h
  obtain ⟨e, he⟩ : ∃ e : Per.Fl l, IsEps e := Model.exists_isEps l
  obtain ⟨-, -, -, -, -, hinj, hk⟩ := thetaP_facts l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ainf_quot_fontaineXi_pow_torsionFree_separated l e he n
  have h3 : ∀ (j : ℕ) (c : Per.Ainf l), xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) ^ j * c → xi e ^ n ∣ c := by
    intro j
    induction j with
    | zero => intro c hc; simpa using hc
    | succ j ih =>
      intro c hc
      refine h1 c (ih _ ?_)
      rwa [← mul_assoc, ← pow_succ]
  have key : ∀ c : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) c ∈ Per.kerP l ^ n ↔
      xi e ^ n ∣ c := by
    intro c
    rw [hk e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    refine ⟨fun ⟨y, hy⟩ => ?_, fun hc => map_dvd _ hc⟩
    obtain ⟨j, d, hd⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    refine h3 j c ⟨d, hinj ?_⟩
    rw [map_mul, map_mul, ← hd, hy, map_pow, map_pow]
    ring
  refine (key a).2 (h2 a fun k => ?_)
  obtain ⟨b, hb⟩ := h k
  exact ⟨b, (key _).1 hb⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatibleStatement
section
open NumberField
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | exact GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
section
open CategoryTheory Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.LabelUniqueAll

open Finset

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    ∀ k, k ≤ d → MvPolynomial.aeval a (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval b (MvPolynomial.esymm (Fin d) ℂ k) := by
  first
  | exact @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | (apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq ..)

theorem map_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have he := esymm_eq_of_psum_eq a b h
  have hp : ((Finset.univ.val.map a).map fun t => X - C t).prod =
      ((Finset.univ.val.map b).map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ), ← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ),
      he j (by simpa [Nat.lt_succ_iff] using hj)]
  have := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact this

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]; omega

variable {g : ℕ} [Fact g.Prime]

theorem natDegree_minpoly_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkd : k ≤ d) : (minpoly (ZMod g) (L.gen d ^ k)).natDegree = d := by
  set γ := L.gen d
  set m := g ^ d - 1 with hmdef
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hord : orderOf γ = m := L.gen_order d hd
  have hγm : γ ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hfix : (γ ^ k) ^ (g ^ d) = γ ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, show g ^ d = m + 1 by omega, pow_succ, hγm, one_mul]
  have hdvd : (minpoly (ZMod g) (γ ^ k)).natDegree ∣ d :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ d).2 hfix
  have hfe : (γ ^ k) ^ (g ^ (minpoly (ZMod g) (γ ^ k)).natDegree) = γ ^ k :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ _).1 dvd_rfl
  have he0 : 0 < (minpoly (ZMod g) (γ ^ k)).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
  generalize (minpoly (ZMod g) (γ ^ k)).natDegree = e at hdvd hfe he0 ⊢
  by_contra hne
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  have hge : 2 ≤ g ^ e := le_trans hg2 (Nat.le_self_pow he0.ne' g)
  have hone : γ ^ (k * (g ^ e - 1)) = 1 := by
    have : γ ^ k * γ ^ (k * (g ^ e - 1)) = γ ^ k * 1 := by
      rw [mul_one, ← pow_add]
      conv_rhs => rw [← hfe, ← pow_mul]
      congr 1
      have : g ^ e = (g ^ e - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hγ0) this
  have hmd : m ∣ k * (g ^ e - 1) := hord ▸ orderOf_dvd_of_pow_eq_one hone
  have hpos : 0 < k * (g ^ e - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hmd
  have hec : e * 2 ≤ e * c := Nat.mul_le_mul_left e hc2
  have h2 : d ≤ 2 * (d - e) := by omega
  have h3 : 2 * (d - e) ≤ 2 ^ (d - e) := two_mul_le_two_pow _
  have h4 : 2 ^ (d - e) ≤ g ^ (d - e) := Nat.pow_le_pow_left hg2 _
  have h5 : d * g ^ e ≤ g ^ d := by
    calc d * g ^ e ≤ g ^ (d - e) * g ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ d := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have h6 : k * (g ^ e - 1) ≤ d * (g ^ e - 1) := Nat.mul_le_mul_right _ hkd
  have h7 : d * (g ^ e - 1) = d * g ^ e - d := Nat.mul_sub_one _ _
  omega

theorem label_eq (L : LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : Gn g d → ℂ)
    (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  obtain ⟨hPl, hc, hval⟩ := h
  obtain ⟨hPl', -, hval'⟩ := h'
  have hd : 0 < d := hc.1
  obtain ⟨x, hx⟩ := LabelUnique.exists_mem hd hPl
  obtain ⟨x', hx'⟩ := LabelUnique.exists_mem hd hPl'
  have hx1 := LabelUnique.pow_sub_one_eq_one hPl hx
  have hx1' := LabelUnique.pow_sub_one_eq_one hPl' hx'
  have hteich : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → L.teich w ^ (g ^ d - 1) = 1 := fun w hw => by
    rw [← map_pow, hw, map_one]
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hγ0 : L.gen d ≠ 0 := by
    have hγm : L.gen d ^ (g ^ d - 1) = 1 := by rw [← L.gen_order d hd]; exact pow_orderOf_eq_one _
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hsums : ∀ k, 1 ≤ k → k ≤ d → ∑ i : Fin d, L.teich (x ^ (g ^ (i : ℕ))) ^ k =
      ∑ i : Fin d, L.teich (x' ^ (g ^ (i : ℕ))) ^ k := by
    intro k hk1 hkd
    have hdeg := natDegree_minpoly_gen_pow L hd hk1 hkd
    obtain ⟨y, hy, hz⟩ := GlobalTheory.GLm.exists_irreducible_charpoly_mem_rootsBar g d (L.gen d ^ k)
      (pow_ne_zero _ hγ0) hdeg
    have e1 := hval x hx y hy _ hz
    have e2 := hval' x' hx' y hy _ hz
    rw [e1] at e2
    have e3 := mul_left_cancel₀ (pow_ne_zero (d - 1) (by norm_num : (-1 : ℂ) ≠ 0)) e2
    have conv : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → ∀ i : ℕ,
        thetaOf L d w ((L.gen d ^ k) ^ (g ^ i)) = L.teich (w ^ (g ^ i)) ^ k := by
      intro w hw i
      rw [← pow_mul, LabelUnique.thetaOf_gen_pow L d hd w (hteich w hw), map_pow, ← pow_mul,
        Nat.mul_comm]
    simp only [conv x hx1, conv x' hx1'] at e3
    rw [Fin.sum_univ_eq_sum_range (fun i => L.teich (x ^ g ^ i) ^ k),
      Fin.sum_univ_eq_sum_range (fun i => L.teich (x' ^ g ^ i) ^ k)]
    exact e3
  have hm := map_eq_of_psum_eq _ _ hsums
  have hmem : L.teich x ∈ Finset.univ.val.map (fun i : Fin d => L.teich (x ^ (g ^ (i : ℕ)))) :=
    Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, by simp⟩
  rw [hm] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have hxe : x = x' ^ (g ^ (i : ℕ)) :=
    L.teich_inj _ _ (LabelUnique.ne_zero_of_mem hPl hx)
      (pow_ne_zero _ (LabelUnique.ne_zero_of_mem hPl' hx')) hi.symm
  have h1 : aeval x P' = 0 := by
    rw [hxe]; exact LabelUnique.aeval_pow_eq_zero (LabelUnique.aeval_eq_zero_of_mem hPl'.1.ne_zero hx') i
  have h2 := minpoly.eq_of_irreducible_of_monic hPl'.2.1 h1 hPl'.1
  rw [h2, LabelUnique.minpoly_eq_of_mem hPl hx]

end GlobalTheory.GLq.LabelUniqueAll

namespace GlobalTheory.GLq

theorem isCuspOf_label_unique_allPrimes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime]
    (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ),
    GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' :=
  fun _ _ _ L d P P' χ h h' => LabelUniqueAll.label_eq L d P P' χ h h'

end GlobalTheory.GLq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteType
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_finite_over_localization_atPrime_below (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by
  classical
  let p : Ideal P := 𝔫.comap (algebraMap P B)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl
  have hMle : M ≤ 𝔫.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ h
    exact hs (Ideal.mem_comap.mpr h)
  have hM0 : M ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    show algebraMap P B s ∈ 𝔫
    rw [h0]
    exact 𝔫.zero_mem
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM0
  let algCA : Algebra (Localization M) A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) A M 𝔫.primeCompl hMle
  have : IsScalarTower B (Localization M) A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  let 𝔪 : Ideal (Localization M) := (maximalIdeal A).comap (algebraMap (Localization M) A)
  have h𝔪 : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  have hNA : IsLocalization (𝔫.primeCompl.map (algebraMap B (Localization M))) A :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  have hunitB : ∀ b : B, IsUnit (algebraMap B A b) ↔ b ∈ 𝔫.primeCompl := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔫 b
  have hA : IsLocalization.AtPrime A 𝔪 := by
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := A)
      (M := 𝔫.primeCompl.map (algebraMap B (Localization M))) (N := 𝔪.primeCompl) ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ h
      have hu : IsUnit (algebraMap B A b) := (hunitB b).mpr hb
      rw [IsScalarTower.algebraMap_apply B (Localization M) A] at hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) hu
    · rintro ⟨x, hx⟩
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
      have key : algebraMap B A b =
          algebraMap B A s * algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s) := by
        rw [IsScalarTower.algebraMap_apply B (Localization M) A b,
          IsScalarTower.algebraMap_apply B (Localization M) A s, ← map_mul, IsLocalization.mk'_spec']
      refine ⟨algebraMap B (Localization M) s, b, ?_, (IsLocalization.mk'_spec' _ _ _).symm⟩
      have hs : IsUnit (algebraMap B A s) := (hunitB s).mpr (hMle s.2)
      have hx' : IsUnit (algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s)) := by
        by_contra hn
        exact hx (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
      refine (hunitB b).mp ?_
      rw [key]
      exact hs.mul hx'
  have hcomapB : 𝔪.comap (algebraMap B (Localization M)) = 𝔫 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A 𝔫
  refine ⟨p, hp, Localization M, inferInstance, inferInstance, inferInstance, inferInstance, algCA,
    𝔪, h𝔪, ?_, hA, ?_⟩
  · exact localizationAlgebra_injective (S := B) (M := p.primeCompl) (Localization.AtPrime p)
      (Localization M) hinj
  · let Q : Ideal (Localization.AtPrime p) :=
      𝔪.comap (algebraMap (Localization.AtPrime p) (Localization M))
    have hQ : Q.comap (algebraMap P (Localization.AtPrime p)) = p := by
      show (𝔪.comap _).comap _ = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq P B (Localization M), ← Ideal.comap_comap, hcomapB]
    have h1 : Q = p.map (algebraMap P (Localization.AtPrime p)) := by
      have h2 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q
      rw [Ideal.under_def, hQ] at h2
      exact h2.symm
    show Q = _
    rw [h1]
    exact Localization.AtPrime.map_eq_maximalIdeal

theorem exists_conductor_adicCompletion_of_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  intro A _ _ _ _ _ _
  obtain ⟨r, B, _, _, _, _, _, _, 𝔫, _, hinj, hloc⟩ := GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial A
  obtain ⟨p, _, C, _, _, _, _, _, 𝔪, _, hinjC, hlocC, hcomap⟩ :=
    exists_finite_over_localization_atPrime_below (MvPolynomial (Fin r) ℤ) B A 𝔫 hinj
  have hTreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain (Localization.AtPrime p)
  have := GlobalTheory.T.isRegularLocalRing_adicCompletion' (Localization.AtPrime p)
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (R := MvPolynomial (Fin r) ℤ)
      (IsLocalization.injective (M := p.primeCompl) (S := Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  have hTU : Function.Injective (algebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro x y h
    exact AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) h
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) C hTU hinjC
  obtain ⟨S', _, e, he⟩ := GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod (Localization.AtPrime p) C A 𝔪 hcomap
  have key := GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor (AdicCompletion (maximalIdeal A) A) S' _ e _ hd
  have hed : (e (algebraMap (Localization.AtPrime p) _ d)).1 =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A (algebraMap _ C d)) := by
    rw [Algebra.TensorProduct.algebraMap_apply', he]
  refine ⟨algebraMap C A (algebraMap _ C d), ?_, fun c hc => ?_⟩
  · intro h0
    apply hd0
    apply hinjC
    apply IsLocalization.injective (M := 𝔪.primeCompl) (S := A) 𝔪.primeCompl_le_nonZeroDivisors
    rw [h0, map_zero, map_zero]
  · obtain ⟨s, hs⟩ := key c hc
    exact ⟨s, by rw [hs, hed]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_inertia_tameChar_other_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TameMove.tameRep_move | exact GlobalTheory.TameMove.tameRep_move | (intros; apply GlobalTheory.TameMove.tameRep_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerRStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  first | exact @GlobalTheory.TameRootSurj.main | exact GlobalTheory.TameRootSurj.main | (intros; apply GlobalTheory.TameRootSurj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
section
open NumberField Formalism.BasicNotions

namespace GlobalTheory.AutLattice

section
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)

theorem finrank_int_eq (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) :
    Module.finrank ℤ L = Module.finrank ℚ E * Module.finrank E V := by
  let _i : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [Module.finrank_mul_finrank ℚ E V,
    IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]
  let f : L →ₗ[ℤ] V := L.subtype.toAddMonoidHom.toIntLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s =>
        (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s
      surj := fun v => by
        obtain ⟨n, hn, h⟩ := exists_int_smul_mem L hL v
        exact ⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := Subtype.ext h
        rw [this]⟩ }
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm

end

theorem card_dvd_minkM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V), L.FG → Submodule.span E (L : Set V) = ⊤ → ∀ G : Subgroup (V ≃ₗ[E] V), Finite G → (∀ g ∈ G, ∀ x ∈ L, g x ∈ L) → Nat.card G ∣ minkM (Module.finrank ℚ E * Module.finrank E V) := by
  intro hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree E V
  have : Module.Free ℤ L := inferInstance
  rw [← finrank_int_eq L hL]
  let b := Module.finBasis ℤ L
  let r : G →* Module.End ℤ L :=
    { toFun := fun g => AddMonoidHom.toIntLinearMap
        { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      map_one' := by ext x; rfl
      map_mul' := fun g h => by ext x; rfl }
  have hr : Function.Injective r := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hL
    intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  let φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply hr
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val hgh
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM _ φ.range (Finite.of_equiv _ e.toEquiv)

end GlobalTheory.AutLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  first | exact @GlobalTheory.TameTau.exists_root_congr_unit | exact GlobalTheory.TameTau.exists_root_congr_unit | (intros; apply GlobalTheory.TameTau.exists_root_congr_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpowStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TamePowTeich.exists_zeta_pow_close | exact GlobalTheory.TamePowTeich.exists_zeta_pow_close | (intros; apply GlobalTheory.TamePowTeich.exists_zeta_pow_close <;> assumption)
end

