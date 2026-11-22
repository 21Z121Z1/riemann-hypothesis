import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.Bundle0005
import Formalism.LocalToGlobal.Columns.Bundle0006
import Formalism.LocalToGlobal.Columns.BaseInst
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct

-- bundled from Formalism.LocalToGlobal.Columns.AtTOwedC
section
open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

theorem owedC_zpow_emod {ζ : K} (hζ : ζ ^ p = 1) (a : ℤ) : ζ ^ (a % (p : ℤ)) = ζ ^ a := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hζ
    exact zero_ne_one hζ
  conv_rhs => rw [← Int.emod_add_mul_ediv a p, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

def owedC_chr (hp : p.Prime) (h : Nat.card A = p) {ζ : K} (hζ : ζ ^ p = 1) : AddChar A K :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  (AddChar.zmodChar p hζ).compAddMonoidHom (owedC_res hp h).toAddEquiv.toAddMonoidHom

theorem owedC_chr_intCast (hp : p.Prime) (h : Nat.card A = p) {ζ : K} (hζ : ζ ^ p = 1) (a : ℤ) :
    owedC_chr hp h hζ (a : A) = ζ ^ a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have e : owedC_chr hp h hζ (a : A) = AddChar.zmodChar p hζ (owedC_res hp h (a : A)) := rfl
  rw [e, owedC_res_intCast, AddChar.zmodChar_apply, ← owedC_zpow_emod hζ a, ← ZMod.val_intCast, zpow_natCast]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

theorem card_quotient_eq_prime (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
  rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def CharT.ofRootMul (hPr : Pr.Ok) (ζ : Pr.Word → X.K) (hζ : ∀ u, ζ u ^ Pr.T u = 1)
    (x : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}), 𝓞 X.E ⧸ P.1.asIdeal) : CharT X Pr where
  psiT u P := AddChar.mulShift (owedC_chr (hPr.T_prime u) (card_quotient_eq_prime hPr u P) (hζ u)) (x u P)

def CharT.ofRoot (hPr : Pr.Ok) (ζ : Pr.Word → X.K) (hζ : ∀ u, ζ u ^ Pr.T u = 1) : CharT X Pr :=
  CharT.ofRootMul hPr ζ hζ fun _ _ => 1

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

def CharT.WeilTied (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (xi0 : X.E) : Prop :=
  ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) (a b : ℤ),
    redP P.1 xi0 * (a : 𝓞 X.E ⧸ P.1.asIdeal) = (b : 𝓞 X.E ⧸ P.1.asIdeal) →
      σ₀ (Ps.psiT u P (a : 𝓞 X.E ⧸ P.1.asIdeal)) = Complex.exp (2 * Real.pi * Complex.I * b / Pr.T u)

def XiUnitT (Pr : Primes X) (xi0 : X.E) : Prop :=
  ∀ u : Pr.Word, ∃ b : ℤ, ¬ (Pr.T u : ℤ) ∣ b ∧
    ∀ P : {P // P ∈ Pr.vT u}, redP P.1 xi0 = (b : 𝓞 X.E ⧸ P.1.asIdeal)

theorem owedC_exp_zpow (n : ℕ) (b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I / n) ^ b = Complex.exp (2 * Real.pi * Complex.I * b / n) := by
  rw [← Complex.exp_int_mul]
  congr 1
  ring

theorem CharT.WeilTied.unique (hPr : Pr.Ok) {Ps Ps' : CharT X Pr} {σ₀ : X.K →+* ℂ} {xi0 : X.E}
    (h : Ps.WeilTied σ₀ xi0) (h' : Ps'.WeilTied σ₀ xi0) : Ps = Ps' := by
  obtain ⟨ψ⟩ := Ps
  obtain ⟨ψ'⟩ := Ps'
  congr 1
  funext u P
  ext c
  obtain ⟨a, rfl⟩ := owedC_exists_int (hPr.T_prime u) (card_quotient_eq_prime hPr u P) c
  obtain ⟨b, hb⟩ := owedC_exists_int (hPr.T_prime u) (card_quotient_eq_prime hPr u P)
    (redP P.1 xi0 * (a : 𝓞 X.E ⧸ P.1.asIdeal))
  exact σ₀.injective ((h u P a b hb).trans (h' u P a b hb).symm)

theorem CharT.WeilTied.ok (hPr : Pr.Ok) {Ps : CharT X Pr} {σ₀ : X.K →+* ℂ} {xi0 : X.E}
    (h : Ps.WeilTied σ₀ xi0) (hxi : XiUnitT Pr xi0) : Ps.Ok where
  ne u P hp := by
    obtain ⟨b, hb, hbP⟩ := hxi u
    have h1 := h u P 1 b (by rw [hbP P]; simp)
    rw [hp, AddChar.one_apply, map_one, ← owedC_exp_zpow] at h1
    exact hb (((Complex.isPrimitiveRoot_exp (Pr.T u) (hPr.T_prime u).ne_zero).zpow_eq_one_iff_dvd b).1 h1.symm)
  same u P P' a := by
    obtain ⟨b, -, hbP⟩ := hxi u
    apply σ₀.injective
    rw [h u P a (b * a) (by rw [hbP P]; push_cast; rfl), h u P' a (b * a) (by rw [hbP P']; push_cast; rfl)]

theorem owedC_exists_exp {K : Type} [Field K] (σ₀ : K →+* ℂ) {n : ℕ} (hn : n ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ζ' : K, σ₀ ζ' = Complex.exp (2 * Real.pi * Complex.I / n) := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective σ₀.injective).eq_pow_of_pow_eq_one
    (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

def CharT.psiC (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ₀ : X.K →* ℂ).compAddChar (Ps.psiT u P)

theorem CharT.psiC_apply (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u})
    (c : 𝓞 X.E ⧸ P.1.asIdeal) : Ps.psiC σ₀ u P c = σ₀ (Ps.psiT u P c) := rfl

theorem CharT.Ok.psiC_ne {Ps : CharT X Pr} (h : Ps.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Ps.psiC σ₀ u P ≠ 1 := by
  intro h1
  apply h.ne u P
  ext c
  apply σ₀.injective
  rw [← CharT.psiC_apply, h1, AddChar.one_apply, AddChar.one_apply, map_one]

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.AtTOwedU
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem SameAt.refl (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) : SameAt Q N N :=
  ⟨1, one_notMem Q, 1, one_notMem Q, fun x hx => by rwa [one_smul], fun x hx => by rwa [one_smul]⟩

theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

theorem conjP_conjP_eq (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem mem_one_of_forall_heightOne {a : E}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • a ∈ (1 : Submodule (𝓞 E) E)) :
    a ∈ (1 : Submodule (𝓞 E) E) := by
  let I : Ideal (𝓞 E) := (1 : Submodule (𝓞 E) E).comap (LinearMap.toSpanSingleton (𝓞 E) E a)
  have hI : ∀ s : 𝓞 E, s ∈ I ↔ s • a ∈ (1 : Submodule (𝓞 E) E) := fun s => Iff.rfl
  by_cases hT : I = ⊤
  · have : (1 : 𝓞 E) ∈ I := hT ▸ Submodule.mem_top
    rw [hI, one_smul] at this
    exact this
  · obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hT
    obtain ⟨s, hs, hsa⟩ := h ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
    exact (hs (hIM ((hI s).2 hsa))).elim

theorem hStd_smul_right' (r : 𝓞 E) (x y : Sp E n) : hStd E n x (r • y) = r • hStd E n x y := by
  rw [← algebraMap_smul E r y, map_smul, algebraMap_smul]

theorem isUnimodular_eq_of_sameAt {M M' : Submodule (𝓞 E) (Sp E n)} (hM : IsUnimodular (hStd E n) M)
    (hM' : IsUnimodular (hStd E n) M')
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), SameAt Q M M' ∨ SameAt (conjPrime₂ Q) M M') : M = M' := by
  refine unimodular_eq_of_le hM hM' fun x hx => ?_
  rw [← show dual (hStd E n) M' = M' from hM', mem_dual]
  intro y hy
  apply mem_one_of_forall_heightOne
  intro Q
  rcases h Q with ⟨a, ha, a', ha', h1, h2⟩ | ⟨a, ha, a', ha', h1, h2⟩
  · refine ⟨a', ha', ?_⟩
    have h3 : a' • x ∈ dual (hStd E n) M' := by
      rw [show dual (hStd E n) M' = M' from hM']
      exact h2 x hx
    have h4 := (mem_dual M' (a' • x)).1 h3 y hy
    rwa [hStd_smul_right'] at h4
  · refine ⟨cO E a, ha, ?_⟩
    have h3 : x ∈ dual (hStd E n) M := by
      rw [show dual (hStd E n) M = M from hM]
      exact hx
    have h4 := (mem_dual M x).1 h3 (a • y) (h1 y hy)
    rwa [hStd_osmul_left, hStd_smul_right'] at h4

theorem sameAt_upA_upN {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    {x : Sp E n} (hx : x ∈ N) : SameAt P (upA P.asIdeal N x) (upN P.asIdeal N x) := by
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hlat huni P hne hx
  obtain ⟨a, ha, haP⟩ := exists_mem_notMem hne
  exact ⟨1, one_notMem P, a, haP, fun y hy => by rw [one_smul]; exact h4 hy,
    fun y hy => h5 (Submodule.smul_mem_smul ha hy)⟩

theorem upN_upN_comm {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) {P P' : HeightOneSpectrum (𝓞 E)} (hne : conjPrime₂ P ≠ P)
    (hne' : conjPrime₂ P' ≠ P') (hPP : P ≠ P') (hPc : P ≠ conjPrime₂ P') (hPc' : P' ≠ conjPrime₂ P) {x x' : Sp E n}
    (hx : x ∈ N) (hx' : x' ∈ N) (hx1 : x ∈ upN P'.asIdeal N x') (hx1' : x' ∈ upN P.asIdeal N x) :
    upN P'.asIdeal (upN P.asIdeal N x) x' = upN P.asIdeal (upN P'.asIdeal N x') x := by
  obtain ⟨l1, u1, s1, -, -⟩ := upN_spec hlat huni P hne hx
  obtain ⟨l1', u1', s1', -, -⟩ := upN_spec hlat huni P' hne' hx'
  obtain ⟨l2, u2, s2, -, -⟩ := upN_spec l1 u1 P' hne' hx1'
  obtain ⟨l2', u2', s2', -, -⟩ := upN_spec l1' u1' P hne hx1
  have good : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ conjPrime₂ P → Q ≠ conjPrime₂ P' →
      SameAt Q (upN P'.asIdeal (upN P.asIdeal N x) x') (upN P.asIdeal (upN P'.asIdeal N x') x) := by
    intro Q hQ hQ'
    by_cases h1 : Q = P
    · subst h1
      have a1 := (s2 Q hPP hQ').symm
      have a2 := (sameAt_upA_upN hlat huni Q hne hx).symm
      have a3 : SameAt Q (upA Q.asIdeal N x) (upA Q.asIdeal (upN P'.asIdeal N x') x) := (s1' Q hPP hQ').sup _
      have a4 := sameAt_upA_upN l1' u1' Q hne hx1
      exact ((a1.trans a2).trans a3).trans a4
    · by_cases h2 : Q = P'
      · subst h2
        have a1 := (sameAt_upA_upN l1 u1 Q hne' hx1').symm
        have a2 : SameAt Q (upA Q.asIdeal (upN P.asIdeal N x) x') (upA Q.asIdeal N x') := ((s1 Q h1 hQ).symm).sup _
        have a3 := sameAt_upA_upN hlat huni Q hne' hx'
        have a4 := s2' Q h1 hQ
        exact ((a1.trans a2).trans a3).trans a4
      · exact (((s2 Q h2 hQ').symm.trans (s1 Q h1 hQ).symm).trans (s1' Q h2 hQ')).trans (s2' Q h1 hQ)
  refine isUnimodular_eq_of_sameAt u2 u2' fun Q => ?_
  by_cases h1 : Q = conjPrime₂ P
  · right
    rw [h1, conjP_conjP_eq]
    exact good P hne.symm hPc
  · by_cases h2 : Q = conjPrime₂ P'
    · right
      rw [h2, conjP_conjP_eq]
      exact good P' hPc' hne'.symm
    · exact Or.inl (good Q h1 h2)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.Ok.up_up_comm {d : Deco E n ST SG} (hd : d.Ok) {P P' : ST} (hP : MoveHyp ST SG P)
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') (q q' : 𝓞 E) {x x' : Sp E n} (hx : x ∈ d.N) (hx' : x' ∈ d.N)
    (hx1 : x ∈ upN P'.1.asIdeal d.N x') (hx1' : x' ∈ upN P.1.asIdeal d.N x) :
    (d.up P q x).up P' q' x' = (d.up P' q' x').up P q x := by
  have hne1 : P.1 ≠ P'.1 := fun h => hne (Subtype.ext h)
  have hN : upN P'.1.asIdeal (upN P.1.asIdeal d.N x) x' = upN P.1.asIdeal (upN P'.1.asIdeal d.N x') x :=
    upN_upN_comm hd.lat hd.uni hP.ne hP'.ne hne1 (hP'.st P) (hP.st P') hx hx' hx1 hx1'
  obtain ⟨l1, u1, s1, -, -⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  obtain ⟨l1', u1', s1', -, -⟩ := upN_spec hd.lat hd.uni P'.1 hP'.ne hx'
  obtain ⟨-, -, s2, -, -⟩ := upN_spec l1 u1 P'.1 hP'.ne hx1'
  obtain ⟨-, -, s2', -, -⟩ := upN_spec l1' u1' P.1 hP.ne hx1
  ext1
  · exact hN
  · funext Q
    by_cases h1 : Q = P
    · subst h1
      rw [Deco.up_f_ne _ _ _ _ hne]
      funext y
      rw [Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ hne]
      have e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P' q' x').N x) = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x) := by
        show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P'.1.asIdeal d.N x') x) = _
        rw [← hN]
        exact (s2 Q.1 hne1 (hP'.st Q)).localization_eq
      rw [e]
    · by_cases h2 : Q = P'
      · subst h2
        rw [Deco.up_f_ne _ _ _ _ h1]
        funext y
        rw [Deco.up_f, Deco.up_f, Deco.up_f_ne _ _ _ _ h1]
        have e : localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.up P q x).N x') = localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x') := by
          show localization₂ Q.1.asIdeal (upN Q.1.asIdeal (upN P.1.asIdeal d.N x) x') = _
          rw [hN]
          exact (s2' Q.1 hne1.symm (hP.st Q)).localization_eq
        rw [e]
      · rw [Deco.up_f_ne _ _ _ _ h2, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h1, Deco.up_f_ne _ _ _ _ h2]
  · rfl

theorem Deco.IsUp.diamond {d d₁ d₂ : Deco E n ST SG} (hd : d.Ok) {P P' : ST} (hP : MoveHyp ST SG P)
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    (hq' : q' ∈ P'.1.asIdeal) (hq2' : q' ∉ P'.1.asIdeal ^ 2) (h1 : Deco.IsUp P q d d₁)
    (h2 : Deco.IsUp P' q' d₁ d₂) : ∃ d₁' : Deco E n ST SG, d₁'.Ok ∧ Deco.IsUp P' q' d d₁' ∧ Deco.IsUp P q d₁' d₂ := by
  obtain ⟨x₀, hx₀, hfx₀, rfl⟩ := h1

  obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime (hP'.st P).symm
  have hmk : Ideal.Quotient.mk P.1.asIdeal a = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.1.asIdeal), Ideal.Quotient.eq, ← hab]
    simpa using Ideal.neg_mem_iff _ |>.2 hb
  have hx : a • x₀ ∈ d.N := d.N.smul_mem a hx₀
  have hfx : d.f P (a • x₀) = 1 := by
    rw [hd.f_smul P a x₀ (le_locP _ _ hx₀), hmk, hfx₀, one_mul]
  have hc : d.up P q x₀ = d.up P q (a • x₀) := by
    apply Deco.up_congr
    have : x₀ - a • x₀ = b • x₀ := by
      rw [show b = 1 - a by rw [← hab]; ring, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hb hx₀
  rw [hc] at h2
  have hd1 : (d.up P q (a • x₀)).Ok := hd.up P hP hq hq2 hx hfx
  obtain ⟨x₀', hx₀', hfx₀', rfl⟩ := h2
  obtain ⟨l1, u1, s1, le1, -⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx

  have hne1 : P.1 ≠ P'.1 := fun h => hne (Subtype.ext h)
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hne1
  have hmk' : Ideal.Quotient.mk P'.1.asIdeal e = 1 := by
    rw [← map_one (Ideal.Quotient.mk P'.1.asIdeal), Ideal.Quotient.eq, ← hee]
    simpa using Ideal.neg_mem_iff _ |>.2 he'
  have hy1 : e • x₀' ∈ upN P.1.asIdeal d.N (a • x₀) := Submodule.smul_mem _ e hx₀'
  have hy : e • x₀' ∈ d.N := smul_upA_mem hx he (le1 hx₀')
  have hfy1 : (d.up P q (a • x₀)).f P' (e • x₀') = 1 := by
    rw [hd1.f_smul P' e x₀' (le_locP _ _ hx₀'), hmk', hfx₀', one_mul]
  have hfy : d.f P' (e • x₀') = 1 := by
    rw [Deco.up_f_ne _ _ _ _ hne.symm] at hfy1
    exact hfy1
  have hc' : (d.up P q (a • x₀)).up P' q' x₀' = (d.up P q (a • x₀)).up P' q' (e • x₀') := by
    apply Deco.up_congr
    have : x₀' - e • x₀' = e' • x₀' := by
      rw [show e' = 1 - e by rw [← hee]; ring, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul he' hx₀'
  obtain ⟨-, -, -, -, ge1'⟩ := upN_spec hd.lat hd.uni P'.1 hP'.ne hy
  have hx1 : a • x₀ ∈ upN P'.1.asIdeal d.N (e • x₀') :=
    ge1' (Submodule.smul_mem_smul ha ((le_sup_left : d.N ≤ upA P'.1.asIdeal d.N (e • x₀')) hx₀))
  refine ⟨d.up P' q' (e • x₀'), hd.up P' hP' hq' hq2' hy hfy, ⟨e • x₀', hy, hfy, rfl⟩, a • x₀, hx1, ?_, ?_⟩
  · rw [Deco.up_f_ne _ _ _ _ hne]
    exact hfx
  · rw [hc']
    exact hd.up_up_comm hP hP' hne q q' hx hy hx1 hy1

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DecoOwed
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem localization_linear_extension_exists (N : Submodule (𝓞 E) (Sp E n)) (P : HeightOneSpectrum (𝓞 E))
    (f0 : N →ₗ[𝓞 E] (𝓞 E ⧸ P.asIdeal)) (x : Sp E n) (hx : x ∈ localization₂ P.asIdeal N) :
    ∃ c : 𝓞 E ⧸ P.asIdeal, ∀ (s : 𝓞 E) (_ : s ∉ P.asIdeal) (h : s • x ∈ N),
      Ideal.Quotient.mk P.asIdeal s * c = f0 ⟨s • x, h⟩ := by
  obtain ⟨s0, hs0, h0⟩ := (mem_locP _ _ _).1 hx
  have := P.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs0)
  refine ⟨b * f0 ⟨s0 • x, h0⟩, fun s _ h => ?_⟩
  have e1 : Ideal.Quotient.mk P.asIdeal s * f0 ⟨s0 • x, h0⟩ = Ideal.Quotient.mk P.asIdeal s0 * f0 ⟨s • x, h⟩ := by
    have a1 : f0 (s • ⟨s0 • x, h0⟩) = s • f0 ⟨s0 • x, h0⟩ := map_smul _ _ _
    have a2 : f0 (s0 • ⟨s • x, h⟩) = s0 • f0 ⟨s • x, h⟩ := map_smul _ _ _
    have a3 : (s • (⟨s0 • x, h0⟩ : N)) = s0 • ⟨s • x, h⟩ := Subtype.ext (smul_comm _ _ _)
    rw [a3, a2] at a1
    rw [Algebra.smul_def, Algebra.smul_def] at a1
    exact a1.symm
  calc _ = b * (Ideal.Quotient.mk P.asIdeal s * f0 ⟨s0 • x, h0⟩) := by ring
    _ = (Ideal.Quotient.mk P.asIdeal s0 * b) * f0 ⟨s • x, h⟩ := by rw [e1]; ring
    _ = _ := by rw [hb, one_mul]

theorem FunAt.exists_ext (N : Submodule (𝓞 E) (Sp E n)) (P : HeightOneSpectrum (𝓞 E))
    (f0 : N →ₗ[𝓞 E] (𝓞 E ⧸ P.asIdeal)) : ∃ F : Sp E n → 𝓞 E ⧸ P.asIdeal,
      FunAt P N F ∧ ∀ x (hx : x ∈ N), F x = f0 ⟨x, hx⟩ := by
  classical
  let F : Sp E n → 𝓞 E ⧸ P.asIdeal := fun x =>
    if h : x ∈ localization₂ P.asIdeal N then (localization_linear_extension_exists N P f0 x h).choose else 0
  have hF : ∀ x (_ : x ∈ localization₂ P.asIdeal N) (s : 𝓞 E) (_ : s ∉ P.asIdeal) (h : s • x ∈ N),
      Ideal.Quotient.mk P.asIdeal s * F x = f0 ⟨s • x, h⟩ := by
    intro x hx s hs h
    simp only [F, dif_pos hx]
    exact (localization_linear_extension_exists N P f0 x hx).choose_spec s hs h
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨t, ht, h'⟩ := (mem_locP _ _ _).1 hy
    have hst : s * t ∉ P.asIdeal := fun h' => (P.isPrime.mem_or_mem h').elim hs ht
    have m1 : (s * t) • x ∈ N := by rw [mul_comm, mul_smul]; exact N.smul_mem _ h
    have m2 : (s * t) • y ∈ N := by rw [mul_smul]; exact N.smul_mem _ h'
    have m3 : (s * t) • (x + y) ∈ N := by rw [smul_add]; exact N.add_mem m1 m2
    apply mul_left_cancel₀ (mk_ne_zero hst)
    rw [mul_add, hF _ hx _ hst m1, hF _ hy _ hst m2, hF _ (Submodule.add_mem _ hx hy) _ hst m3, ← map_add]
    congr 1
    exact Subtype.ext (smul_add _ _ _)
  · intro a x hx
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
    have m1 : s • (a • x) ∈ N := by rw [smul_comm]; exact N.smul_mem _ h
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [hF _ (Submodule.smul_mem _ a hx) _ hs m1, mul_left_comm, hF _ hx _ hs h]
    have : (⟨s • a • x, m1⟩ : N) = a • ⟨s • x, h⟩ := Subtype.ext (smul_comm _ _ _)
    rw [this, map_smul, Algebra.smul_def]; rfl
  · intro x hx
    simp only [F, dif_neg hx]
  · intro x hx
    have := hF x (le_locP _ _ hx) 1 (one_notMem P) (by simpa using hx)
    rw [map_one, one_mul] at this
    rw [this]; congr 1; exact Subtype.ext (one_smul _ _)

end Formalism.L2.Col
end
end

