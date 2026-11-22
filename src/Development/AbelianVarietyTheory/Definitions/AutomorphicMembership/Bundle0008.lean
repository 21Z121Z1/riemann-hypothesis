import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
section
noncomputable section

namespace GlobalTheory.HeightCounting.ReadingModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain

def ofFrame {D : D7} (F : TwFrame D) : TwFrameC D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩

def toFrame {D : D7} (F : TwFrameC D) : TwFrame D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩

theorem twTiedC_iff {D : D7} (F : TwFrameC D) : TwistFrameLowIndexCompatibility D F (lowPr D) ↔ NTwTied D (toFrame F) := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E)
  constructor
  · intro T
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN]),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (by simp [lowPr]), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (by simp [lowPr]),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd])⟩
  · intro T
    refine ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos, fun i p hp => ?_⟩
    simp only [lowPr, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · exact T.S0x_contains_two_places i
    · exact T.S0x_contains_q0_places i
    · exact T.S0x_contains_ccK_places i p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    · exact T.S0x_contains_ramified_places i p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

theorem twTiedC_of_tied {D : D7} {F : TwFrame D} (T : NTwTied D F) : TwistFrameLowIndexCompatibility D (ofFrame F) (lowPr D) :=
  (twTiedC_iff (ofFrame F)).2 T

theorem twConjAt_of_choiceC {D : D7} {C : NChoice D} (h : ChoiceC D C) : TwConjAt D C :=
  fun w hw => ⟨h.conj w hw, h.sd_conj w hw⟩

theorem choiceC_int {D : D7} {C : NChoice D} (h : ChoiceC D C) (w : D.what₂.places.Pl) (hw : TwistedAt D w) (x : D.LL0) :
    (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) ∈
        (algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w)))).range ↔
      fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) ∈
        (algebraMap (C.Oe w) (FractionRing (C.Oe w))).range := by
  rw [← h.emb_side w hw x, ← C.embW_w, h.sd_place w hw x]

section
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}

theorem ringSpec_onto (S : RingSpec D cf b0 b1 Sx T) (w : HeightOneSpectrum (𝓞 ↥D.LL0)) :
    ∃ i, ((T.l i : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal := by
  refine ⟨S.eTw.symm w, ?_⟩
  have h := (S.pl_emb (S.eTw.symm w)).1
  rwa [Equiv.apply_symm_apply] at h

theorem embedding_mem_coefficient_field (S : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (x : ↥D.LL0) : S.j0 i x ∈ (S.K0 i).1 := by
  obtain ⟨⟨y, z⟩, hyz⟩ := IsLocalization.surj (nonZeroDivisors (T.O0 i)) (T.emb0 i x)
  have hz : (z : T.O0 i) ≠ 0 := nonZeroDivisors.ne_zero z.2
  have h := (S.ringSpec_baseEmbedding_compatible i x y z hz).mp hyz
  have hz' : ((S.eO0 i z : intOf (T.l i) (S.K0 i).1) : PadicAlgCl (T.l i)) ≠ 0 := by
    intro h0
    apply hz
    exact (S.eO0 i).map_eq_zero_iff.mp (Subtype.ext h0)
  have hx : S.j0 i x = (S.eO0 i y : PadicAlgCl (T.l i)) / (S.eO0 i z : PadicAlgCl (T.l i)) := by
    rw [eq_div_iff hz', h]
  rw [hx]
  exact (S.K0 i).1.div_mem (S.eO0 i y).2.1 (S.eO0 i z).2.1

variable (hE : IsEmpty D.nd.Loc) (F : TwF T) (S : RingSpec D cf b0 b1 Sx T)
  (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
  (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex)

def withRings : D7 := setTw D (T.ntw hE F (TwL.empty T)) ex h0 th S.br S.br_ind

def chiData : NChiData (withRings hE F S ex h0 th) :=
  ⟨S.mu0H, S.etaH, S.delH, fun a => hE.elim a, fun _ a => PEmpty.elim a, S.embO⟩

theorem chiTied : NormalizedCharacterCompatibility (withRings hE F S ex h0 th) (chiData hE F S ex h0 th) :=
  ⟨fun a => hE.elim a, S.del_fix, S.delta, S.chi1, S.ringSpec_sidedEmbedding_fixedField, S.etaT_unr, S.etaT_inf, fun _ a => PEmpty.elim a⟩

def charFrame : CharFrame (withRings hE F S ex h0 th) :=
  ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩

theorem deltaRead : DeltaRead (withRings hE F S ex h0 th) (charFrame hE F S ex h0 th) := S.deltaRead

def frameC : TwFrameC (withRings hE F S ex h0 th) :=
  ⟨S.K0, S.eO0, S.j0, S.Lw, S.eO, S.eOk, S.iCq, fun _ => Sx⟩

theorem tiedC (low : Finset ℕ) (hlow : ∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx)
    (hconj : ∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx)
    (hk : ∀ (i : (withRings hE F S ex h0 th).ntw.Tw) j b k P, P ∉ (withRings hE F S ex h0 th).ntw.S0 i → ∃ s : Multiset (FractionRing ((withRings hE F S ex h0 th).ntw.O i)),
      (LinearMap.charpoly ((withRings hE F S ex h0 th).ntw.hk i j b k P)).map
        (algebraMap ((withRings hE F S ex h0 th).ntw.O i) (FractionRing ((withRings hE F S ex h0 th).ntw.O i))) =
        (s.map fun a => Polynomial.X - Polynomial.C a).prod)
    (hB : ∀ i j b, LinearMap.range ((withRings hE F S ex h0 th).nexp.embB i j b) =
      (withRings hE F S ex h0 th).nexp.Bsup i j b ⊓
        (NForms.V0 (withRings hE F S ex h0 th) i j b).restrictScalars ((withRings hE F S ex h0 th).ntw.O i))
    (hs : ∀ i (s s' : F.Sig i), F.jS i s = F.jS i s' → F.side i s = F.side i s' →
      (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → F.hEig i s k P = F.hEig i s' k P) → s = s') :
    TwistFrameLowIndexCompatibility (withRings hE F S ex h0 th) (frameC hE F S ex h0 th) low :=
  ⟨fun i => ⟨S.eTw i, S.pl_emb i⟩, S.ringSpec_baseIntegersEquiv_algebraMap, S.ringSpec_baseEmbedding_compatible, S.eO_alg, S.eOk_alg, S.mu_g, hk, S.ringSpec_excludedPlaces_eq, fun _ => hconj, hB, hs,
    fun _ a => PEmpty.elim a, fun _ => hlow⟩

end

end GlobalTheory.HeightCounting.ReadingModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Deg

variable {T : Type} {a b : ℕ}

open Classical in

def monoDeg (e : DVar T a b →₀ ℕ) (τ : T) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

theorem monoDeg_eq_sum [Fintype T] (e : DVar T a b →₀ ℕ) (τ : T) : monoDeg e τ = ∑ β, ∑ α, e (τ, β, α) := by
  unfold monoDeg
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ e.support) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk
    simp [hk])]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp [Fintype.sum_prod_type]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem exists_monoDeg [Fintype T] (ha : 0 < a) (hb : 0 < b) (n : T → ℕ) : ∃ e : DVar T a b →₀ ℕ, ∀ τ, monoDeg e τ = n τ := by
  classical
  refine ⟨∑ t, Finsupp.single (t, (⟨0, hb⟩ : Fin b), (⟨0, ha⟩ : Fin a)) (n t), fun τ => ?_⟩
  rw [monoDeg_eq_sum, Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
  · rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · intro α _ hα
      simp [Finsupp.finsetSum_apply, Ne.symm hα]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro β _ hβ
    refine Finset.sum_eq_zero fun α _ => ?_
    simp [Finsupp.finsetSum_apply, Ne.symm hβ]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Deg

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

abbrev Sb (a : I.ι) (u : B.Word) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) :=
  Sall (Pr := B.primes X) I.sel (I.tup a) u

abbrev modulus (a : I.ι) (u : B.Word) : ℕ :=
  cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u

end ColIn

abbrev nuDeg (B : Base) (u : B.Word) (i : ℕ) (τ : B.fields.Tau) : ℤ := ∑ r, (B.wts.nuW u (i + 1) τ).w r

theorem nuDeg_nonneg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) : 0 ≤ nuDeg B u i τ := by
  have h0 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
  unfold nuDeg
  refine Finset.sum_nonneg fun r _ => le_trans h0 ?_
  unfold DomWeight.detShift
  split_ifs with h
  · apply DomWeight.anti
    rw [Fin.le_iff_val_le_val]
    have := r.isLt
    simp only
    omega
  · exact absurd (lt_of_le_of_lt (Nat.zero_le _) r.isLt) h

theorem exists_monoDeg_nuDeg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    ∃ e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ, ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ := by
  have hk := B.R.m_add_three_le_k
  have h1 : 0 < B.R.N i := by
    show 0 < B.R.k + i * (B.R.t + 1)
    omega
  have h2 : 0 < B.R.N (i + 1) := by
    show 0 < B.R.k + (i + 1) * (B.R.t + 1)
    omega
  obtain ⟨e, he⟩ := exists_monoDeg (T := B.fields.Tau) h1 h2 (fun τ => (nuDeg B u i τ).toNat)
  exact ⟨e, fun τ => by rw [he τ]; exact Int.toNat_of_nonneg (nuDeg_nonneg B u hi τ)⟩

private theorem monoDeg_eq_sum_filter {T : Type} {a b : ℕ} {d : DecidableEq T} (e : DVar T a b →₀ ℕ) (τ : T) :
    monoDeg e τ = ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k := by
  unfold monoDeg
  congr

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

def jetNum (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1)))
    (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) : ℂ :=
  (I.A.chiF _ _ N N')⁻¹ * jetC I.A.cD (I.A.thInd (I.Sb a u) N N' c x) e

abbrev JetRange (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : Prop :=
  letI := B.fields.starE
  InRange (I.Sb a u) (I.modulus a u) c N N' x

def JetsIn : Prop :=
  ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
    JetsRatDeg I.A (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (fun τ => ∑ r, (B.wts.nuW u (i + 1) τ).w r)

theorem jetsIn_iff : I.JetsIn ↔ ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → ∀ N N' c x,
    I.JetRange a u i N N' c x → ∀ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) →
      I.jetNum a u i N N' c x e ∈ B.embLL.fieldRange := by
  constructor
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := h a u i hi N N' c x hx e (fun τ => by rw [← monoDeg_eq_sum_filter]; exact he τ)
    refine RingHom.mem_fieldRange.mpr ⟨y, ?_⟩
    rw [← I.A_σ₀]
    exact hy
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp
      (h a u i hi N N' c x hx e (fun τ => by rw [monoDeg_eq_sum_filter]; exact he τ))
    refine ⟨y, ?_⟩
    rw [I.A_σ₀]
    exact hy

theorem jetRange_std (a : I.ι) (u : B.Word) (i : ℕ) :
    I.JetRange a u i (stdLat B.fields.E (B.R.N i)) (stdLat B.fields.E (B.R.N (i + 1))) 1 0 := by
  letI := B.fields.starE
  show IsSdLat _ ∧ IsSdLat _ ∧ 0 < 1 ∧ 1 ∣ _ ∧ _
  exact ⟨And.intro Formalism.L2.Col.stdLat_lattice Formalism.L2.Col.stdLat_unimodular,
    And.intro Formalism.L2.Col.stdLat_lattice Formalism.L2.Col.stdLat_unimodular, Nat.one_pos, one_dvd _, zero_mem _⟩

variable {I} {a : I.ι} {u : B.Word} {i : ℕ} {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))}
  {N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))} {c : ℕ} {x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))}
  {e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ}

theorem JetsIn.exists_eq (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : ∃ y : B.LL, B.embLL y = I.jetNum a u i N N' c x e := by
  exact RingHom.mem_fieldRange.mp ((jetsIn_iff I).mp h a u i hi N N' c x hx e he)

theorem JetsIn.isAlgebraic (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : IsAlgebraic ℚ (I.jetNum a u i N N' c x e) := by
  obtain ⟨y, hy⟩ := h.exists_eq hi hx he
  rw [← hy]
  exact IsAlgebraic.algHom B.embLL.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic y)

end ColIn

example {B : Base} {X : PreX B.toPre} (I : ColIn B X) (h : I.JetsIn) (u : B.Word) (i : ℕ) (hi : i < B.R.m) :
    ∃ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) ∧
      I.jetNum I.mu0 u i (stdLat _ _) (stdLat _ _) 1 0 e ∈ B.embLL.fieldRange := by
  obtain ⟨e, he⟩ := exists_monoDeg_nuDeg B u hi
  exact ⟨e, he, h.exists_eq hi (I.jetRange_std _ u i) he⟩

example {B : Base} {X : PreX B.toPre} (I : ColIn B X) (u : B.Word) (i : ℕ) (hi : i < B.R.m) (e)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ)
    (ht : Transcendental ℚ (I.jetNum I.mu0 u i (stdLat _ _) (stdLat _ _) 1 0 e)) : ¬ I.JetsIn :=
  fun h => ht (h.isAlgebraic hi (I.jetRange_std _ u i) he)

example : monoDeg (Finsupp.single ((true, 0, 1) : DVar Bool 2 1) 3) true = 3 ∧
    monoDeg (Finsupp.single ((true, 0, 1) : DVar Bool 2 1) 3) false = 0 := by
  simp [monoDeg_eq_sum, Finsupp.single_apply, Prod.ext_iff]

example {T : Type} [Fintype T] {a b : ℕ} (cD : T → ℂ) (G : VCx T a b → ℂ) : jetC cD G 0 = G 0 := by
  have h : ∀ (n : ℕ) (_ : n = 0) (v : Fin n → VCx T a b), iteratedFDeriv ℂ n G 0 v = G 0 := by
    rintro _ rfl v
    simp
  simp only [jetC, derivAt0, Finsupp.prod_zero_index, one_mul]
  exact h _ (by simp) _

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPlacesOverOfIsConjPl
section
noncomputable section

namespace GlobalTheory.HeightCounting.LabConjModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem mem_Ine_of_transport {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) {t γ : G E Ω}
    (hγ : ∀ x, γ (c x) = c (t x)) (ht : t ∈ Ine (F := E) A) : γ ∈ Ine (F := E) B := by
  have key : ∀ y, γ y ∈ B ↔ y ∈ B := fun y => by
    obtain ⟨x, rfl⟩ := c.surjective y
    rw [hγ, ← hc, ← hc, apply_mem_iff_of_mem_Dec ht.1]
  refine ⟨?_, fun y hy => ?_⟩
  · show γ • B = B
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key, mul_inv_apply]
  · obtain ⟨x, rfl⟩ := c.surjective y
    rw [hγ, ← map_sub, val_lt_iff c hc]
    exact ht.2 x ((A.valuation_le_one_iff x).2 ((hc x).2 ((B.valuation_le_one_iff _).1 hy)))

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem exists_isConjPl (w : PlE H) : ∃ w', IsConjPl H w w' :=
  ⟨w.comap (conjInt H).symm.toRingHom (conjInt H).symm.surjective, isConjPl_iff.2 fun x => by
    simp [HeightOneSpectrum.comap]⟩

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem mem_placesOver_of_isConjPl {w₀ w : PlE H} (h : IsConjPl H w₀ w) {p : ℕ} (hp : w₀ ∈ placesOver H.E p) :
    w ∈ placesOver H.E p := by
  have := (isConjPl_iff.1 h _).1 hp
  rwa [map_natCast] at this

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_place (D : D7) (k : Fin 2) :
    ∃ v w, IsConjPl D.host (D.naut.plGw k v) w ∧ ∀ v', w ≠ D.naut.plGw k v' := by
  have hpos : 0 < Fintype.card (D.nd.PlG k) := by
    rw [D.nd.card_PlG]; unfold Ranks.f Ranks.n; positivity
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hpos
  obtain ⟨w, hw⟩ := exists_isConjPl (D.naut.plGw k v)
  exact ⟨v, w, hw, fun v' e => D.naut.plGw_nconj k v v' (e ▸ hw)⟩

theorem natDegree_labLP {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (hL : LabConj D T) (k v) (w : PlE D.host)
    (hw : IsConjPl D.host (D.naut.plGw k v) w) (a : D.naut.LP w) :
    (D.naut.items₂ k w a).natDegree = (T.e w a).lpTame.lpDim := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, γ, -, h2, h3, h4⟩ := hL k v w hw
  rw [h4 a]
  exact WD.natDegree_lab ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
    (mem_placesOver_of_isConjPl hw (D.naut.plGw_over k v)),
    mem_Ine_of_transport c h2 h3 (D.ntypes.tg_mem k v), D.ntypes.teichC_inj k⟩ _

theorem roots_labLP {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (hL : LabConj D T) (k v) (w : PlE D.host)
    (hw : IsConjPl D.host (D.naut.plGw k v) w) : ∃ (c : D.nd.Om ≃+* D.nd.Om) (γ : G D.host.E D.nd.Om),
      γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧ ∀ a : D.naut.LP w,
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w a)).map (D.ntypes.teichC k) = (T.e w a).tameEig γ := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, γ, -, h2, h3, h4⟩ := hL k v w hw
  have hγ := mem_Ine_of_transport c h2 h3 (D.ntypes.tg_mem k v)
  refine ⟨c, γ, hγ, h3, fun a => ?_⟩
  rw [h4 a]
  exact WD.map_rootsBar_lab ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
    (mem_placesOver_of_isConjPl hw (D.naut.plGw_over k v)), hγ, D.ntypes.teichC_inj k⟩ _

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩

set_option maxHeartbeats 1000000 in

theorem exists_labTrue_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) a := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x a) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.LabConjModel

end
end

