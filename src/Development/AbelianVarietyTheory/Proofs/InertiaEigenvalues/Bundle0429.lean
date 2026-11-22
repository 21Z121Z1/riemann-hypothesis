import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCover
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe

namespace GlobalTheory.SplitType

theorem exists_sqrt (l d : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hj : jacobiSym (-(d : ℤ)) l = 1) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) ∧ ‖2 * s‖ = 1 := by
  have hd : ¬ (l : ℤ) ∣ (d : ℤ) := by
    intro h
    have : jacobiSym (-(d : ℤ)) l = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h.neg_right
    omega
  have h2' : ¬ (l : ℤ) ∣ 2 := fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))
  have one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1 := fun k hk =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (l : ℤ) ∣ a ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have ha' : ¬ (l : ℤ) ∣ 2 * a := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · exact h2' h
    · exact hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d a (by
    rw [one_of _ ha', one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 ha)
  have hs2 : s ^ 2 = -(d : ℤ_[l]) := by
    rw [sq, ← hs]; simp
  refine ⟨s, hs2, ?_⟩
  have n2 : ‖(2 : ℤ_[l])‖ = 1 := by simpa using one_of 2 h2'
  have nd : ‖(d : ℤ_[l])‖ = 1 := by simpa using one_of d hd
  have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, nd]
  rw [norm_mul, n2, one_mul]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

theorem exists_root {l d : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] (f : ℤ_[l] →+* A)
    {s : ℤ_[l]} (hs : s ^ 2 = -(d : ℤ_[l])) {y : A} (hy : y ^ 2 = -(d : A)) :
    ∃ t : ℤ_[l], (t = s ∨ t = -s) ∧ f t = y := by
  have : y ^ 2 = (f s) ^ 2 := by rw [← map_pow, hs, hy]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · exact ⟨s, Or.inl rfl, h.symm⟩
  · exact ⟨-s, Or.inr rfl, by rw [map_neg, h]⟩

section Host
variable {R : Ranks} (H : Host R)

theorem sqrtE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem map_sqrt_sq {A : Type} [CommRing A] (φ : H.E →+* A) : φ (H.sqd) ^ 2 = -(H.d : A) := by
  rw [← map_pow, sqrtE_sq]; simp

theorem conj_sqrtE : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  have h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [conj_sqrt, map_neg, h]
  simp

theorem isIntegral_sqrtE : IsIntegral ℤ (H.sqd) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sqrtE_sq]
  exact (isIntegral_natCast _).neg

end Host

section Loc
variable (D : D7) (i : D.nd.Loc)

theorem root_of_embIn (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {s₀ t : ℤ_[D.nd.l i]}
    (h₀ : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (algebraMap ℤ_[D.nd.l i] (D.nd.O i) s₀) =
      D.nd.embK i (D.embE (D.host.sqd)))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    (EmbIn (N := D.nd) D.nbr i true w hw τ → t = s₀) ∧
      (EmbIn (N := D.nd) D.nbr i false w hw τ → t = -s₀) := by
  have e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i]) := by
    rw [← τ.commutes]
    exact congrArg τ (Subtype.ext ht.symm)
  have e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i]) := by
    rw [← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]
    rfl
  have e3 : D.what₂.embLL (D.embE (D.host.sqd)) =
      Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem
  have inj := (algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
    have : y = D.embE (D.host.sqd) :=
      D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))
    rw [this, e1, e2] at hy
    exact Subtype.ext (inj hy).symm
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' := (mem_halfType_false D.host φ).1 hφ
    have : y = -D.embE (D.host.sqd) :=
      D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])
    rw [this, e1, map_neg, map_neg, e2, ← map_neg] at hy
    exact Subtype.ext (inj hy).symm

theorem mem_iff_norm (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : 𝓞 D.host.E) (z : ℤ_[D.nd.l i])
    (hz : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (z : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))) :
    x ∈ w.asIdeal ↔ ‖z‖ < 1 := by
  rw [bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]

theorem root_ne (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hn : ‖2 * t‖ = 1)
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  let β : 𝓞 D.host.E := ⟨D.host.sqd, isIntegral_sqrtE D.host⟩
  have hβ : (β : D.host.E) = D.host.sqd := rfl
  set n : ℕ := t.zmodRepr with hn'
  have h1 : ‖t - n‖ < 1 := PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)
  have hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n := by
    simp [← hβ]
  have hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n := by
    simp [← hβ]
  have h2 : β - n ∈ w.asIdeal := (mem_iff_norm D i w hw _ (t - n) (by
    rw [hx, map_sub, map_sub, ← ht]; simp)).2 h1
  have h3 : -β - n ∈ w'.asIdeal := (hc (β - n) (-β - n) (by
    rw [hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2
  have h4 : ‖-t - n‖ < 1 := (mem_iff_norm D i w' hw' _ (-t - n) (by
    rw [hy, map_sub, map_sub, map_neg, map_neg, ← ht']; simp)).1 h3
  have h5 : 2 * t = (t - n) + -(-t - n) := by ring
  have h6 := PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))
  rw [← h5, hn, norm_neg] at h6
  exact absurd h6 (not_le.2 (max_lt h1 h4))

end Loc

theorem place_type_conj : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) →
    ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' →
      (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
        (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  intro D i hl w w' hw hw' hc
  obtain ⟨-, h5, hq, hd, -, hcls⟩ := hl
  have h2 : D.nd.l i ≠ 2 := by omega
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := by
    by_contra hj
    simp only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls
    split_ifs at hcls
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

end GlobalTheory.SplitType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixEquivariantHomCommFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mreal_hom_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f _ Y hY
  set L := bk.evW with hL
  set Φ : WCb l →+* WCb l := (frobW l).toRingHom with hΦ
  have hc : ∀ x, L (frobS l bk.a x) = Φ (L x) := by
    intro x
    simp only [hL, hΦ, BK.evW, RingHom.comp_apply, bk.ev_frob, AlgHom.coe_toRingHom]
    exact (frobW_inclW _).symm
  have hsm : ∀ {m n : Type} (c : bk.S) (M : Matrix m n bk.S), (c • M).map L = L c • M.map L := by
    intro m n c M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply]
  have hTΦ : ∀ {m n : Type} (M : Matrix m n (WCb l)), M.map (frobW l) = M.map Φ := fun _ => rfl
  have hz : (zW f).map Φ = zW f := by
    ext i j; simp [zW, hΦ, Matrix.map_apply]
  have hYΦ : (Y.map (frobS l bk.a)).map L = (Y.map L).map Φ := by
    refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply]; exact hc _
  have φT := hT.φ
  have φT' := hT'.φ
  rw [hTΦ] at φT φT'
  have hYf : T'.map Φ * (Y.map L).map Φ = zW f * T.map Φ := by
    rw [← Matrix.map_mul, hY, Matrix.map_mul, hz]
  have key : T' * (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L =
      T' * (bk.E ^ S'.a • (Y * S.A)).map L := by
    rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hYΦ, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← φT', map_pow, map_pow, Matrix.smul_mul, smul_smul, hYf, hY, Matrix.mul_assoc,
      ← φT, Matrix.mul_smul, smul_smul, mul_comm]
  obtain ⟨u, hu⟩ := hT'.unit
  have key2 : (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L = (bk.E ^ S'.a • (Y * S.A)).map L := by
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) key
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    exact this
  have hinj := (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.1
  refine Matrix.ext fun i j => ?_
  exact hinj (congrFun (congrFun key2 i) j)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatio
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem tc_injective (l : ℕ) [Fact l.Prime] : Function.Injective (tc l) := by
  intro a b hab
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  have hinj := GlobalTheory.MemLoc.crisP_injective l j hj
  have key : ∀ y : Formalism.Per.Fl l, j (tc l y) =
      algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l)
        (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.tm y)) := by
    intro y
    have := hj.on0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) (Formalism.Per.tm y))
    rw [Subalgebra.coe_algebraMap, ← GlobalTheory.RingIface.tower] at this
    exact this
  have h1 := congrArg j hab
  rw [key, key] at h1
  have h2 := (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2
    (GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l h1)
  have h3 := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h2
  simpa using h3

theorem teich_eq_of_phi_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 →
    φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  intro l _ w' ζ hw h
  have hφ : φc l w' ≠ 0 := ((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 w' hw).1
  have hprod : w' * φc l w' ≠ 0 := by
    intro h0
    rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h0 | h0
    · exact hw h0
    · exact hφ h0
  rw [map_mul, frob_teich] at h
  have h' : (tc l (ζ ^ l) - tc l ζ) * (w' * φc l w') = 0 := by
    linear_combination h
  rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h' with h0 | h0
  · exact tc_injective l (sub_eq_zero.1 h0)
  · exact absurd h0 hprod

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBLocalDegreeSumBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.QDDeg

theorem locDeg_sum_le_and_ge : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  intro D h1 i hi s hs
  have hl : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  obtain ⟨hpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  refine ⟨(hsum s hs).trans hfr.le, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have he : w.asIdeal.ramificationIdx ℤ = 2 := ((h1 _ hmem).2 w (hs w hw)).1
  have hp := hpos w
  unfold Formalism.MainNotions.N.locDeg at hp ⊢
  rw [he] at hp ⊢
  omega

end GlobalTheory.Proof.QDDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBRamifiedPrimesNeTypePrimes
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTensorInj
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensor

theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, GlobalTheory.LocIota.tied_ιB_algebraMap_Kur l P AI T c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCoverStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_eq_along_latticeTowerCover : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ), 1 ≤ a → ∀ (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (σ : GQ l) (U : Matrix (Fin Cv.d) (Fin Cv.d) (ℂ_[l])) (U' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (ℂ_[l])) (Bd : ℝ) (S : ℕ → ℂ_[l]), S 0 = a → (∀ i j, ‖U i j‖ ≤ Bd) → (∀ m i j, ‖U' m i j‖ ≤ Bd) → (∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹) → (∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i • ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n) → ∀ n, (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
  first | exact @GlobalTheory.CoverTrace.trace_pow_eq | exact GlobalTheory.CoverTrace.trace_pow_eq | (intros; apply GlobalTheory.CoverTrace.trace_pow_eq; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_system_monomial_products_basis : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (t : ℕ → MvPolynomial ℕ R), (∀ i, ∃ (v : Rˣ) (a b : MvPolynomial ℕ R), a ∈ MvPolynomial.supported R (Set.Iio i) ∧ b ∈ MvPolynomial.supported R (Set.Iio i) ∧ t i = MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) → LinearIndependent R (fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) ∧ Submodule.span R (Set.range fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) = ⊤ := by
  first | exact @GlobalTheory.TriBasis.tri_basis | exact GlobalTheory.TriBasis.tri_basis | (intros; apply GlobalTheory.TriBasis.tri_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLineAdmissibleCocyclesNotIndependentStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialLine_admissibleCocycles_not_independent : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  first | exact @GlobalTheory.TopSteps.TrivLine.main | exact GlobalTheory.TopSteps.TrivLine.main | (intros; apply GlobalTheory.TopSteps.TrivLine.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProofStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof : StepDeg := by
  first | exact @GlobalTheory.Pass.stepDeg_main | exact GlobalTheory.Pass.stepDeg_main | (intros; apply GlobalTheory.Pass.stepDeg_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttachedStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → UnrRho i s := by
  first | exact @GlobalTheory.TripleUnramified.unrRho_of_tripleAtt | exact GlobalTheory.TripleUnramified.unrRho_of_tripleAtt | (intros; apply GlobalTheory.TripleUnramified.unrRho_of_tripleAtt <;> assumption)
end

