import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ShiftedParametersOfDifferingLetters

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open scoped nonZeroDivisors NumberField

theorem szf_finrankE (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  omega

theorem szf_finrankF (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]

theorem szf_normG (D : D7) : SzfNormG D := by
  unfold SzfNormG
  rw [FractionalIdeal.absNorm_span_singleton]
  have hE := szf_finrankE D
  have hg : Formalism.MainNotions.S.gE D = algebraMap ℚ D.host.E ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) := by
    simp [Formalism.MainNotions.S.gE]
  rw [hg, Algebra.norm_algebraMap, hE]
  simp only [Formalism.MainNotions.S.gg]
  push_cast
  rw [abs_of_nonneg (by positivity), ← pow_mul, mul_comm D.R.f 2]

theorem szf_finrankFE (D : D7) : Module.finrank D.host.F D.host.E = 2 := by
  have h1 := D.host.der.finrank_E
  have h2 := D.host.der.finrank_F
  have h3 : Module.finrank ℚ D.host.F * Module.finrank D.host.F D.host.E = Module.finrank ℚ D.host.E :=
    Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [h1, h2] at h3
  rw [h1] at hpos
  have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h4

theorem szf_rd_pow (D : D7) : (D.host.rdE ^ D.R.f) ^ 2 = |(NumberField.discr D.host.E : ℝ)| := by
  have hE := szf_finrankE D
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : 0 < D.R.f := by omega
  have hx0 : (0 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := abs_nonneg _
  unfold Formalism.BasicNotions.Host.rdE
  rw [hE, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have hc : (1 : ℝ) / ((2 * D.R.f : ℕ) : ℝ) * ((D.R.f * 2 : ℕ) : ℝ) = 1 := by
    rw [mul_comm D.R.f 2]
    exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (by omega))
  rw [hc, Real.rpow_one]

theorem szf_normDD (D : D7) (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : SzfNormDD D := by
  unfold SzfNormDD
  rw [szf_rd_pow D, hd]
  have hFE := szf_finrankFE D
  have gen : ∀ I : Ideal (𝓞 D.host.F), Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) I) =
      Ideal.absNorm I ^ Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) := by
    intro I
    rw [← Ideal.absNorm_relNorm (𝓞 D.host.F), Ideal.relNorm_algebraMap, map_pow]
  have n2 : ∀ (K : Type) [Field K] [NumberField K],
      (Algebra.norm ℤ (2 : 𝓞 K)).natAbs = 2 ^ Module.finrank ℚ K := by
    intro K _ _
    rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hR : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
    have h2 := gen (Ideal.span {(2 : 𝓞 D.host.F)})
    rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.absNorm_span_singleton,
      Ideal.absNorm_span_singleton, n2, n2, szf_finrankE D, szf_finrankF D, ← pow_mul] at h2
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [szf_finrankE D] at hpos
    have h4 : D.R.f * Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = D.R.f * 2 := by
      rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have key : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F))) = Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ 2 := by
    rw [gen, hR]
  have hc : FractionalIdeal.absNorm (Formalism.MainNotions.S.ddE D) =
      (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (differentIdeal ℤ (𝓞 D.host.F))) : ℚ) := by
    first
    | exact FractionalIdeal.coeIdeal_absNorm _
    | exact FractionalIdeal.absNorm_coeIdeal _
    | exact FractionalIdeal.coe_absNorm _
  have hd2 : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) = (NumberField.discr D.host.F).natAbs := by
    exact NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)
  rw [hc, key, hd2]
  push_cast
  first
  | simp [abs_pow, Nat.cast_natAbs]
  | rw [Nat.cast_natAbs, Int.cast_abs, abs_pow]

theorem separation_bound (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ K0 Cl0 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu CT : ℝ),
      K0 ≤ D.R.k → Cl0 ≤ Cl → LocalBesselAndTopKernel.MassRatioTheoremTwo D large₂ C0 C' Cl Cg cb Cu cT CT C4 c5 CA := by
  obtain ⟨K0, Cl0, h⟩ := separation_bound_of_norms CA c5 C4 C0 cT hCA hcT
  refine ⟨K0, Cl0, fun D large₂ C' Cl Cg cb Cu CT hK hCl => ?_⟩
  intro hh
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := hh.1
    exact hd
  exact h D large₂ C' Cl Cg cb Cu CT (szf_normDD D hd) (szf_normG D) hK hCl hh

theorem family_separation_bound (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ Cl0 : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (Cg cb Cu CT : ℝ), Cl0 ≤ sCl Fm →
      LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT → LocalBesselAndTopKernel.SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 →
      LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter Fm C0 Cg cb Cu cT CT c5 CA := by
  obtain ⟨K0, Cl0, h⟩ := separation_bound CA c5 C4 C0 cT hCA hcT
  refine ⟨max Cl0 (max 1 K0), fun {eps} Fm Cg cb Cu CT hCl hA hE => ?_⟩
  simp only [LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart, LocalBesselAndTopKernel.SchurOrthogonalityRealPlace, LocalBesselAndTopKernel.UnderF, OwnEv] at hA hE ⊢
  obtain ⟨xa, hxa⟩ := hA
  obtain ⟨xe, hxe⟩ := hE
  refine ⟨max xa xe, fun x hx i hh => ?_⟩
  have hCl0 : Cl0 ≤ sCl Fm := le_trans (le_max_left _ _) hCl
  have h1 : (1 : ℝ) ≤ sCl Fm := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hK0 : K0 ≤ sCl Fm := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  have hK : K0 ≤ ((Fm.D x i).R.k : ℝ) := by
    obtain ⟨-, hS, -⟩ := hh
    obtain ⟨-, -, h3, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := hS
    have hk4 : ((Fm.D x i).R.m : ℝ) ^ 4 ≤ ((Fm.D x i).R.k : ℝ) := by exact_mod_cast h3.trans h4
    have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := le_trans h1 hClm
    have hm4 : ((Fm.D x i).R.m : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 4 := le_self_pow₀ hm1 (by norm_num)
    linarith
  exact h (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) Cg cb Cu CT hK hCl0 hh
    (hxa x (le_trans (le_max_left _ _) hx) i hh) (hxe x (le_trans (le_max_right _ _) hx) i hh)

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EqualFlagsScalar : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [NumberField E] [StarRing E] [Algebra K E] (S : HSpace E) (r : ℕ) (T : E)
    (F F' : FlagG S r T), T ≠ 0 →
    (∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x) →
    (∀ j, F'.Xa j = F.Xa j) → F'.Xplus = F.Xplus → Relevant K F F' →
    ∃ c : E, c * star c = 1 ∧ (∀ a, F'.e a - c • F.e a ∈ F.Xa a.val) ∧ F'.z - c • F.z ∈ F.X

def ScalarRootOfUnity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E) (Λ : Submodule (𝓞 E) S.V)
    (F F' : LFlag S r T) (c : E), StarConj E →
    F'.fl.z ∈ Λ → (∀ d : E, d • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = d) →
    c * star c = 1 → F'.fl.z - c • F.fl.z ∈ Xsp F → F'.fl.X = F.fl.X →
    ∃ o : 𝓞 E, (o : E) = c ∧ ∃ N : ℕ, 0 < N ∧ o ^ N = 1

def ScalarCongruentOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F F' : LFlag S r (T : E)) (o : 𝓞 E),
    Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → F.fl.z ∈ Λ → IsAdmissible Λ g F F' →
    F'.fl.z - (o : E) • F.fl.z ∈ Xsp F →
    ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → (T : 𝓞 E) ∉ P.asIdeal → o - 1 ∈ P.asIdeal

def RootsOfUnityFormal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R) (N : ℕ) (g1 g2 : ℕ) (P1 P2 : Ideal R), 0 < N → ζ ^ N = 1 →
    g1.Prime → g2.Prime → g1 ≠ g2 → P1 ≠ ⊤ → P2 ≠ ⊤ → (g1 : R) ∈ P1 → (g2 : R) ∈ P2 → ζ - 1 ∈ P1 → ζ - 1 ∈ P2 → ζ = 1

def ExistsPrimeAbove : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal

def UnitriangularFrameLift (D : D7) : Prop :=
  ∀ (T : D.host.E) (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F F' : LFlag (hS D) D.R.rS T),
    FixedHyp D Λ F → IsLift Λ F' → IsFixedConv Λ (gS D) F' →
    (∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) → F'.fl.z - F.fl.z ∈ Xsp F →
    ∃ n ∈ NLam Λ F, ∀ a, n (F.fl.e a) = F'.fl.e a

theorem id_coprime_notMem {R : Type} [CommRing R] (P : Ideal R) (hP : P ≠ ⊤) (a b : ℕ) (h : Nat.Coprime a b)
    (ha : (a : R) ∈ P) : (b : R) ∉ P := by
  intro hb
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h' : ((Nat.gcd a b : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [Nat.Coprime.gcd_eq_one h] at h'
  have h'' : (1 : R) = (a : R) * (Nat.gcdA a b : R) + (b : R) * (Nat.gcdB a b : R) := by
    have := congrArg (fun z : ℤ => (z : R)) h'
    push_cast at this
    exact this
  rw [h'']
  exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)

theorem cIdFlag_of_steps (h1 : EqualFlagsScalar) (h2 : ScalarRootOfUnity) (h3 : ScalarCongruentOne) (h4 : RootsOfUnityFormal) (h5 : ExistsPrimeAbove) {D : D7}
    (X : TermTie D) (hL : UnitriangularFrameLift D)
    (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1) : UnitaryVolumeMass.cIdFlag D X := by
  rintro u t ⟨hXa, hXp⟩ hrel
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  obtain ⟨c, hcc, he, hz⟩ := h1 D.host.F D.host.E (hS D) D.R.rS _ (X.fl t).fl (X.fl' t).fl hT0 (tie_trace D.sp.cm)
    hXa hXp ((X.rel_iff t).1 hrel)
  have hX : (X.fl' t).fl.X = (X.fl t).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := h2 D.host.E (hS D) D.R.rS _ (X.abelian₂ t) (X.fl t) (X.fl' t) c (p_starConj D)
    (X.lift' t).1 (X.fixed t).2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine h3 D.host.E (hS D) D.R.rS (Tu D u) (X.abelian₂ t) (gS D) (X.fl t) (X.fl' t) o (X.fixed t).2.1
      (X.fixed t).2.2.1.1 (X.adm t) (by rw [ho]; exact hz) P ?_ ?_
    · unfold gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := h5 D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := h5 D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := h4 (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := hL _ (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fixed t) (X.lift' t) (X.conv' t) he hz
  refine (X.isId_iff t).2 ⟨n, hn, hne, ?_⟩
  have hzo : (X.fl t).fl.z ∈ orth (hS D) (Xsp (X.fl t)) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (X.fl t).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have : n (X.fl t).fl.z - (X.fl' t).fl.z =
      (n (X.fl t).fl.z - (X.fl t).fl.z) - ((X.fl' t).fl.z - (X.fl t).fl.z) := by abel
  rw [this]
  exact Submodule.sub_mem _ h3' hz

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.WeightedProjectionSumSelfAdjoint
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S ContinuousLinearMap
open scoped InnerProductSpace

section Toolkit

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def t76L : (E →L[ℂ] E) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ E) ∘ₗ (ContinuousLinearMap.coeLM ℂ)

def t76 (T : E →L[ℂ] E) : ℝ := (t76L T).re

structure IsOrthogonalProjection (P : E →L[ℂ] E) : Prop where
  idem : P.comp P = P
  sa : adjoint P = P

theorem IsOrthogonalProjection.compl {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) : IsOrthogonalProjection (ContinuousLinearMap.id ℂ E - P) := by
  constructor
  · ext x
    have := congrArg (fun T : E →L[ℂ] E => T x) h.idem
    simp only [ContinuousLinearMap.comp_apply] at this
    simp [this]
  · rw [map_sub, h.sa]
    congr 1
    exact ((eq_adjoint_iff _ _).2 (fun x y => rfl)).symm

theorem IsOrthogonalProjection.norm_le {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have h1 : ⟪P x, P x⟫_ℂ = ⟪x, P x⟫_ℂ := by
    have : ⟪P x, P x⟫_ℂ = ⟪x, (adjoint P) (P x)⟫_ℂ := (adjoint_inner_right P x (P x)).symm
    rw [this, h.sa]
    have h2 := congrArg (fun T : E →L[ℂ] E => T x) h.idem
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h2]
  have h3 : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ := by
    have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
    have h5 : (⟪P x, P x⟫_ℂ).re = ‖P x‖ ^ 2 := by simpa using h4
    rw [← h5, h1]
    exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  by_cases h0 : ‖P x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end Toolkit

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem IsOrthogonalProjection.app {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) (x : E) : P (P x) = P x := by
  have h2 := congrArg (fun T : E →L[ℂ] E => T x) h.idem
  simpa using h2

end Abstract

section CorF

variable {W : Type} {C : W → Type} [∀ u, NormedAddCommGroup (C u)] [∀ u, InnerProductSpace ℂ (C u)]
  [∀ u, FiniteDimensional ℂ (C u)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (Ws : Finset W) (P : ∀ u, C u →L[ℂ] H) (c : W → ℝ) (Pu : ∀ u, C u →L[ℂ] C u) (Pi : H →L[ℂ] H)

def q76 (u : W) : H →L[ℂ] H := (P u).comp ((Pu u).comp (adjoint (P u)))

def weightedProjectionSum : H →L[ℂ] H := ∑ u ∈ Ws, (c u : ℂ) • q76 P Pu u

def gramBlock' (u u' : W) : C u' →L[ℂ] C u := (adjoint (P u)).comp (P u')

def compressedProjectionSum : H →L[ℂ] H :=
  ∑ u ∈ Ws, (c u : ℂ) • (Pi.comp ((P u).comp ((Pu u).comp ((adjoint (P u)).comp Pi))))

variable {P c Pu Pi}

end CorF

section CorFNum

variable {W : Type} {C : W → Type} [∀ u, NormedAddCommGroup (C u)] [∀ u, InnerProductSpace ℂ (C u)]
  [∀ u, FiniteDimensional ℂ (C u)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (Ws : Finset W) {P : ∀ u, C u →L[ℂ] H} {c : W → ℝ} {Pu : ∀ u, C u →L[ℂ] C u} {Pi : H →L[ℂ] H}

end CorFNum

section CorFRecord

variable (D : D7) (large₂ : SizeData₂ D)

end CorFRecord

section CorFFamily

variable {eps : ℝ} (Fm : FamP eps)

end CorFFamily

end Formalism.MainNotions.BridgeLemma

end
end

