import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogSubstExpSubOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0003
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem exists_mul_add_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    ∃ t : 𝓞 E, ∃ a ∈ w.asIdeal, t * s + a = 1 :=
  w.isMaximal.exists_inv hs

theorem decoration_admissible_of_localization_eq {d : Deco E n ST SG} (hd : d.Ok) {N' : Submodule (𝓞 E) (Sp E n)}
    (hl : Submodule.IsLattice E N') (hu : IsUnimodular (hStd E n) N')
    (hT : ∀ P : ST, localization₂ P.1.asIdeal d.N = localization₂ P.1.asIdeal N')
    (hG : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal N') :
    Deco.Ok (⟨N', d.f, d.be⟩ : Deco E n ST SG) where
  lat := hl
  uni := hu
  f_add P x hx y hy := hd.f_add P x ((hT P).ge hx) y ((hT P).ge hy)
  f_smul P a x hx := hd.f_smul P a x ((hT P).ge hx)
  f_off P x hx := hd.f_off P x fun h => hx ((hT P).le h)
  f_ne P := by
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    have hx' := Formalism.L2.Col.le_locP P.1 _ hx
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hT P).le hx')
    refine ⟨s • x, h, ?_⟩
    change d.f P (s • x) ≠ 0
    rw [hd.f_smul P s x hx']
    haveI := P.1.isPrime
    exact mul_ne_zero (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)) hne
  be_add w x hx y hy := hd.be_add w x ((hG w).ge hx) y ((hG w).ge hy)
  be_smul w a x hx := hd.be_smul w a x ((hG w).ge hx)
  be_off w x hx := hd.be_off w x fun h => hx ((hG w).le h)
  be_surj w c := by
    obtain ⟨x, hx, hc⟩ := hd.be_surj w c
    have hx' := Formalism.L2.Col.le_locP w.1 _ hx
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hG w).le hx')
    obtain ⟨t, a, ha, e⟩ := exists_mul_add_eq_one_of_notMem w.1 hs
    refine ⟨(t * s) • x, by rw [mul_smul]; exact N'.smul_mem t h, ?_⟩
    change d.be w ((t * s) • x) = c
    have e1 : Ideal.Quotient.mk w.1.asIdeal (t * s) = 1 := by
      have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, add_zero, map_one] at this
    rw [hd.be_smul w _ x hx', e1, one_smul, hc]
  be_ker w x hx h0 := by
    change x ∈ N' at hx
    change d.be w x = 0 at h0
    change x ∈ w.1.asIdeal • N'
    have hx' : x ∈ d.at w.1 := (hG w).ge (Formalism.L2.Col.le_locP w.1 _ hx)
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 hx'
    have h1 : s • x ∈ w.1.asIdeal • d.N := hd.be_ker w _ h (by rw [hd.be_smul w s x hx', h0, smul_zero])
    have h2 : w.1.asIdeal • d.N ≤ localization₂ w.1.asIdeal (w.1.asIdeal • N') := by
      refine Submodule.smul_le.2 fun a ha y hy => ?_
      obtain ⟨u, hu, hy'⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hG w).le (Formalism.L2.Col.le_locP w.1 _ hy))
      refine (Formalism.L2.Col.mem_locP _ _ _).2 ⟨u, hu, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem_smul ha hy'
    obtain ⟨u, hu, h3⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 (h2 h1)
    have hus : u * s ∉ w.1.asIdeal := fun hm => (w.1.isPrime.mem_or_mem hm).elim hu hs
    obtain ⟨t, a, ha, e⟩ := exists_mul_add_eq_one_of_notMem w.1 hus
    have e2 : x = t • (u • s • x) + a • x := by
      rw [← mul_smul, ← mul_smul, ← add_smul, mul_assoc, e, one_smul]
    rw [e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ t h3) (Submodule.smul_mem_smul ha hx)

omit [StarRing E] in

theorem exists_coprime_mem (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ Q ∈ S, ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal) : ∃ a : ℕ, a.Coprime p ∧ ∀ Q ∈ S, ((a : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
  classical
  have h1 : ∀ Q : S, ∃ a : ℕ, a.Coprime p ∧ ((a : ℕ) : 𝓞 E) ∈ Q.1.asIdeal := by
    intro Q
    haveI := Q.1.isMaximal
    haveI : Finite (𝓞 E ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
    letI := Ideal.Quotient.field Q.1.asIdeal
    have hp : (ringChar (𝓞 E ⧸ Q.1.asIdeal)).Prime := CharP.prime_ringChar _
    refine ⟨_, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hS Q.1 Q.2 ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 dvd_rfl
  choose a ha ha' using h1
  refine ⟨∏ Q, a Q, Nat.Coprime.prod_left fun Q _ => ha Q, fun Q hQ => ?_⟩
  exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨Q, hQ⟩))) (ha' ⟨Q, hQ⟩)

end Deco

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem natCast_notMem_of_coprime {a p : ℕ} (h : a.Coprime p) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := 𝓞 K) h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hw)))

omit [Fintype ι] in
theorem nsmul_mem_tauLat (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    {y : Fin n → K} (hy : y ∈ tauLat emb τ L) : a • y ∈ tauLat emb τ L' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a • x, h x hx, ?_⟩
    funext i
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in
theorem localization_dualFr_tauLat_le (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (dualFr (tauLat emb τ L')) ≤ localization₂ w.asIdeal (dualFr (tauLat emb τ L)) := by
  refine GlobalTheory.TransLoc.localization_le_of_smul_mem w ha fun φ hφ x hx => ?_
  have := hφ _ (nsmul_mem_tauLat emb τ h hx)
  rw [dotProduct_smul] at this
  rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
  exact this

theorem localization_nabK_delK_congr (lam : ι → DomWeight n) {M M' : ι → Submodule (𝓞 K) (Fin n → K)}
    (hM : ∀ τ, Submodule.IsLattice K (M τ)) (hM' : ∀ τ, Submodule.IsLattice K (M' τ)) (w : HeightOneSpectrum (𝓞 K))
    (h : ∀ τ, localization₂ w.asIdeal (M τ) = localization₂ w.asIdeal (M' τ)) :
    localization₂ w.asIdeal (nabK lam M) = localization₂ w.asIdeal (nabK lam M') ∧
      localization₂ w.asIdeal (delK lam M) = localization₂ w.asIdeal (delK lam M') := by
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have hB' : ∀ τ, IsBasisAt w (M' τ) (B τ) := fun τ => (h τ).symm.trans (hB τ)
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have h2 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M' hM' w B hB'
  have key : ∀ (T : Submodule (𝓞 K) (Pol K ι n)) (x : VV K lam),
      x ∈ localization₂ w.asIdeal (T.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔ x.1 ∈ localization₂ w.asIdeal T := by
    intro T x
    exact Iff.rfl
  constructor
  · ext x
    unfold nabK
    rw [key, key, h1.1, h2.1]
  · ext x
    unfold delK
    rw [key, key, h1.2, h2.2]

theorem localization_nabAtr_delAtr_congr (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr emb lam L) = localization₂ w.asIdeal (nabAtr emb lam L') ∧
      localization₂ w.asIdeal (delAtr emb lam L) = localization₂ w.asIdeal (delAtr emb lam L') :=
  localization_nabK_delK_congr lam
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L' hL')) w
    fun τ => le_antisymm (localization_dualFr_tauLat_le emb τ h' w ha) (localization_dualFr_tauLat_le emb τ h w ha)

end Coef

variable {p : ℕ} {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem use₃ (lam : X.Tau → DomWeight n) (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal)
    (d : DecoSet X.E n ST SG) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (nabAtr X.emb lam d.1.N) ∧
      localization₂ w.asIdeal (delAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (delAtr X.emb lam d.1.N) := by
  obtain ⟨a, hap, ha⟩ := exists_coprime_mem p ST hT
  refine localization_nabAtr_delAtr_congr X.emb lam d.2.Lsh_lattice d.2.lat (a := a) (fun x hx => ?_)
    (fun x hx => Submodule.smul_of_tower_mem _ a (d.2.N_le_Lsh hx)) w (natCast_notMem_of_coprime hap w hw)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
  exact d.2.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact ha P.1 P.2) hx

theorem levFam_chr_root (Λ : LevFam X.E X.K n SG) (g : Λ.grp) : ∃ k : ℕ, 0 < k ∧ Λ.chr g ^ k = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  haveI : Finite (GLG X.E n SG) := inferInstance
  refine ⟨orderOf g, orderOf_pos g, ?_⟩
  rw [← map_pow, pow_orderOf_eq_one, map_one]

def psysForm (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG)
    (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) (hG : ∀ Q ∈ SG, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) :
    PSys X n p lam (formGSD (roundPk X lam fun d : DecoSet X.E n ST SG => d.1.Lsh) Λ) where
  u := MonoidHom.fst _ _
  chr := Λ.chr.comp (MonoidHom.snd _ _)
  eV := LinearEquiv.refl _ _
  N d := d.1.N
  Aw d d' := SameOff p d.1.N d'.1.N ∧ d.1.f = d'.1.f ∧ d.1.be = d'.1.be
  aw_equiv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl⟩, fun h => ⟨fun Q hQ => (h.1 Q hQ).symm, h.2.1.symm, h.2.2.symm⟩,
      fun h h' => ⟨fun Q hQ => (h.1 Q hQ).trans (h'.1 Q hQ), h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩⟩
  aw_smul g d d' h := by
    refine ⟨fun Q hQ => ?_, ?_, ?_⟩
    · ext x
      change x ∈ localization₂ Q.asIdeal (gmap g.1.1 d.1.N) ↔ x ∈ localization₂ Q.asIdeal (gmap g.1.1 d'.1.N)
      rw [mem_localization_gmap, mem_localization_gmap, h.1 Q hQ]
    · change (d.1.act g.1.1 g.2.1).f = (d'.1.act g.1.1 g.2.1).f
      simp only [Deco.act, h.2.1]
    · change (d.1.act g.1.1 g.2.1).be = (d'.1.act g.1.1 g.2.1).be
      simp only [Deco.act, h.2.2]
  aw_off _ _ h := h.1
  aw_ex d N' hl hu hs := by
    refine ⟨⟨⟨N', d.1.f, d.1.be⟩, decoration_admissible_of_localization_eq d.2 hl hu (fun P => hs _ (hT _ P.2)) fun w => hs _ (hG _ w.2)⟩,
      ⟨⟨hs, rfl, rfl⟩, rfl⟩, ?_⟩
    rintro d' ⟨⟨-, hf, hb⟩, hN⟩
    exact Subtype.ext (Deco.ext hN hf.symm hb.symm)
  lat d := d.2.lat
  uni d := d.2.uni
  N_smul _ _ := rfl
  chr_root g := levFam_chr_root Λ g.2
  rho _ _ := rfl
  del d w hw x := by
    rw [← (use₃ lam hT d w hw).2]
    rfl
  nab d w hw x := by
    rw [← (use₃ lam hT d w hw).1]
    rfl

def psysCol {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (u : Pr.Word) (j : ℕ)
    (hT : ∀ Q ∈ Pr.vT u, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) (hG : ∀ Q ∈ Pr.vGs, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) :
    PSys X (R.N j) p (W.lamTrue u j) (colGSD W Ch u j) :=
  psysForm (W.lamTrue u j) (colLev Ch j) hT hG

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpSNegSumBivariatePairIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OrbitPair

open MvPowerSeries

theorem expS_neg_sum_bivariate_pair_integral : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} [NeZero n'] (om om' : Fin (n' / 2) → ℂ_[p]) (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ om om' s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → Formalism.MainNotions.GL3Theta.SimeqW (MvPowerSeries.subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) → ∃ V : MvPowerSeries (ZMod n') ℂ_[p], Formalism.MainNotions.GL3Theta.IntegralW V ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) := by
  intro p _ σ n' _ om om' b0 bv t x _hb0 hbv ht hx hlaS htx hsim
  classical
  have hxS : HasSubst x := hasSubst_of_constantCoeff_zero fun r => (hx r).2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have hzcc : ∀ s : ZMod n', constantCoeff (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = 0 := by
    intro s
    rw [← hlaS s]
    exact constantCoeff_subst_eq_zero htS ht (GlobalTheory.BeProps.constantCoeff_laS s)
  have hzS : HasSubst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) := hasSubst_of_constantCoeff_zero hzcc
  have hzOm : ∀ s : ZMod n', subst x (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = GlobalTheory.ThStr.laS p n' s := by
    intro s
    rw [← hlaS s, subst_comp_subst_apply htS hxS]
    have : (fun r => subst x (t r)) = (X : ZMod n' → MvPowerSeries (ZMod n') ℂ_[p]) := funext htx
    rw [this, subst_self]
    rfl
  have hFx : subst x (subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) = subst (GlobalTheory.ThStr.laS p n') bv := by
    rw [subst_comp_subst_apply hzS hxS]
    congr 1
    funext s
    exact hzOm s
  have hGx : subst x (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) =
      ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)) := by
    rw [← coe_substAlgHom hxS, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coe_substAlgHom hxS, GlobalTheory.ThBe0.Inhab.subst_powerSeriesEvalTwoGroups hxS (GlobalTheory.ThBe0.Inhab.cc_lg _) (GlobalTheory.ThBe0.Inhab.cc_lg _)]
    simp only [GlobalTheory.ThBe0.lg]
    rw [GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _), GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _),
      subst_X hxS, subst_X hxS]
  obtain ⟨hD0, hDint⟩ := hsim
  set F := subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv with hF
  set G := ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r)) with hG
  have ccL : constantCoeff (subst (GlobalTheory.ThStr.laS p n') bv) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => GlobalTheory.BeProps.constantCoeff_laS s)
      (fun s => GlobalTheory.BeProps.constantCoeff_laS s) hbv
  have ccD : constantCoeff (subst x (F - G)) = 0 := constantCoeff_subst_eq_zero hxS (fun r => (hx r).2) hD0
  have hneg : -(subst x G) = subst x (F - G) + -(subst (GlobalTheory.ThStr.laS p n') bv) := by
    rw [subst_sub hxS, hFx]
    ring
  refine ⟨subst x (Formalism.MainNotions.TaylorLogMetric.expMv (F - G)), ?_, ?_⟩
  · exact GlobalTheory.SubringSeries.subst_mem (A := Formalism.MainNotions.GL3Theta.Wp p) hxS (fun r => (hx r).1) hDint
  · rw [← hGx, hneg]
    show PowerSeries.subst _ (PowerSeries.exp ℂ_[p]) = _ * PowerSeries.subst _ (PowerSeries.exp ℂ_[p])
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ccD (by rw [map_neg, ccL, neg_zero]), GlobalTheory.BeProps.expMv_eq_subst hD0,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp x (fun r => (hx r).2) hD0]

end GlobalTheory.OrbitPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobSign

theorem frobG_isArithFrob_and_sign : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d →
    (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧
    ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  intro D l hl h2 hq hd
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hall : ∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q :=
    fun Q _ _ => GlobalTheory.FrobEmb.isArithFrobAt_frobG D l hl.out Q
  refine ⟨hall, ?_⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  have h := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.1
  rw [hg] at h
  exact h

end GlobalTheory.FrobSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RepConjUniq

theorem main : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i x ρ ρ' h1 h2
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin
  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    rw [h1.2.2 w hso B σ hB' hσ, h2.2.2 w hso B σ hB' hσ]
  have hall := GlobalTheory.BaseChangeConj.charpoly_eq_of_dense' ρ ρ' h1.1 h2.1 _ hdense hfrob
  exact hBN _ _ ρ ρ' h1.2.1 h2.2.1 hall

end GlobalTheory.RepConjUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeSplitOneOfCharTied
section
namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.integral_jets_realPlace_local_bases

theorem tauEmb_ringHom (D : D7) {p : ℕ} [Fact p.Prime] (lm : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ g : D.host.E →+* ℂ_[p], ∀ x, tauEmb D lm τ x = g x := by
  have hm : ∀ x, embT D τ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  exact ⟨lm.comp ((embT D τ).codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

theorem jetsIntegral_basR : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  intro D cD hD N N' L L' hA p _ lm B B' κ hB hB' hκ F hF
  refine (GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames D N N' p lm (YYl D L L') F).2 hF _ _ ?_
  rintro ⟨j1, a, b⟩
  by_cases h0 : lamC lm (cD (tauPl D j1)) = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun ⟨τ, k1, k2⟩ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs with h
    · subst h
      have : κ (tauPl D j1) = 0 := by
        have := hκ (tauPl D j1); rw [h0, norm_zero] at this; exact norm_le_zero_iff.1 this
      simp [this]
    · rfl
  · set τ0 := tauPl D j1 with hτ0
    set c := κ τ0 / lamC lm (cD τ0) with hc
    have hcn : ‖c‖ ≤ 1 := by
      rw [hc, norm_div]; exact div_le_one_of_le₀ (hκ τ0) (norm_nonneg _)
    obtain ⟨n, r, aa, hr, haa, hsum⟩ := GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hD p lm τ0
    obtain ⟨m, r', A, hr', hA', hAsum⟩ :=
      GlobalTheory.T.matrixUnit_integral_comb_embedded_homs D N N' L L' hA p lm τ0 (B τ0) (B' τ0) (hB τ0) (hB' τ0) a b
    refine ⟨n * m, fun t => c * r (finProdFinEquiv.symm t).1 * r' (finProdFinEquiv.symm t).2,
      fun t => aa (finProdFinEquiv.symm t).1 • A (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
    · intro t
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖r _‖ * ‖r' _‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hr _
            · exact hr' _
        _ = 1 := by norm_num
    · intro t
      exact Submodule.subset_span ⟨aa _, haa _, A _, hA' _, rfl⟩
    · rintro ⟨τ, k1, k2⟩
      obtain ⟨g, hg⟩ := tauEmb_ringHom D lm τ
      rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      have key : ∑ i : Fin n, ∑ j : Fin m, c * r i * r' j * tauEmb D lm τ ((aa i • A j) k1 k2)
          = c * ((∑ i, r i * tauEmb D lm τ (aa i)) * (∑ j, r' j * tauEmb D lm τ (A j k1 k2))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, Matrix.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [key, hsum τ]
      split_ifs with h1 h2 h2
      · subst h2
        rw [← hAsum k1 k2, hc, ← mul_assoc, div_mul_cancel₀ _ h0, mul_assoc]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
end GlobalTheory.Proof.integral_jets_realPlace_local_bases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | exact GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecompositionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.jumpIn_of_reads | exact GlobalTheory.HTW.Rec.jumpIn_of_reads | (intros; apply GlobalTheory.HTW.Rec.jumpIn_of_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDualStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) := by
  first | exact @GlobalTheory.TieLat.tie_AA_fg_and_sd | exact GlobalTheory.TieLat.tie_AA_fg_and_sd | (intros; apply GlobalTheory.TieLat.tie_AA_fg_and_sd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiInvarianceRamifiedPlaceFlat
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.phi_invariance_ramified_place_flat : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (sharp : Bool) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → (qOf P.1).Prime → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 → P.1 ∈ Pr.vGs → sharp = false → ∀ κ ∈ Jat (Pr := Pr) (R := R) sharp (i + 1) P.1, ∀ x, PhiAt Ch mu sharp i P.1 (κ.toLinearMap ∘ₗ x) * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) = lamRow Ch mu sharp (i + 1) P.1 κ.toLinearMap * PhiAt Ch mu sharp i P.1 x := by
  intro X Pr R Ch sel S mu cst sharp i P hi _ _ _ _ κ hκ x
  exact GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst sharp hi P hκ x
end

