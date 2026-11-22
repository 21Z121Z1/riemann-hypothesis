import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicExtremalNegativeFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtensionStatement
section
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLine_degree_invariant_finite_extension : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k'] (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) → ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ), (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite → (Function.support ρ).Finite ∧ lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  first | exact @GlobalTheory.FlatLine.lineDeg_descent | exact GlobalTheory.FlatLine.lineDeg_descent | (intros; apply GlobalTheory.FlatLine.lineDeg_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfPoint
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.HSElim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_eq_zero_of_point {F K : Type} [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
    {N e δ : ℕ} {P : Ideal (MvPolynomial (Fin N) F)} {f : MvPolynomial (Fin (e + 1) × Fin N) F}
    (hf : IsChowFormInt P e δ f) (s : Fin (e + 1) → Fin N → K) (y : Fin N → K) (hy : y ≠ 0)
    (hyP : ∀ a ∈ P, aeval y a = 0) (hs : ∀ i, ∑ j, s i j * y j = 0) :
    aeval (fun p : Fin (e + 1) × Fin N => s p.1 p.2) f = 0 := by
  let φ : K ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F K (AlgebraicClosure F)
  have hmap : ∀ {σ : Type} (x : σ → K) (a : MvPolynomial σ F),
      aeval (fun i => φ (x i)) a = φ (aeval x a) := fun x a =>
    (AlgHom.congr_fun (MvPolynomial.comp_aeval (f := x) (φ : K →ₐ[F] AlgebraicClosure F)) a).symm
  have key : aeval (fun p : Fin (e + 1) × Fin N => φ (s p.1 p.2)) f = 0 := by
    refine (hf.zero_iff _).2 ⟨fun j => φ (y j), ?_, fun a ha => ?_, fun i => ?_⟩
    · intro h
      apply hy
      funext j
      have := congrFun h j
      simpa using this
    · rw [hmap, hyP a ha, map_zero]
    · have := congrArg φ (hs i)
      simpa [map_sum, map_mul] using this
  rw [hmap (fun p : Fin (e + 1) × Fin N => s p.1 p.2)] at key
  simpa using key

theorem exists_elim_form : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ)
    (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime →
    (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) →
    ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I →
    ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ D * d * hilbertDegree I ∧
      ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin D → Fin N → K)
        (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 →
        (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hp hcomp hdim hg hgI
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have hIh := GlobalTheory.ChowExists.isHomogeneous_of_component hcomp
  obtain ⟨f0, hf0⟩ := GlobalTheory.ChowExists.exists_isChowFormInt hp hIh hdim
  obtain ⟨i0, hi0⟩ := GlobalTheory.ChowExists.exists_X_notMem hf0
  have hJh := isHomogeneous_sup_span_singleton hIh hg
  have hex : ∀ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset,
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) F, IsChowFormInt P e (hilbertDegree P) f := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    have hPp := hP.1.1.1
    obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup hIh hdim hg hgI hP
    obtain rfl : e = e' := by omega
    exact GlobalTheory.ChowExists.exists_isChowFormInt hPp (isHomogeneous_of_mem_projComponents hJh hP) h2
  choose! f hf using hex
  refine ⟨∏ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, f P, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun P hP => (hf P hP).ne_zero
  · refine (totalDegree_finsetProd _ _).trans ?_
    have h1 : ∑ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, (f P).totalDegree =
        (e + 1) * projSetDegree (I ⊔ Ideal.span {g}) := by
      rw [projSetDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P hP => GlobalTheory.ChowSection.totalDegree_of_isChowFormInt (hf P hP)
    rw [h1, mul_assoc]
    exact Nat.mul_le_mul_left _ (projSetDegree_sup_le_of_isPrime hIh hi0 hg hgI)
  · intro K _ _ _ s y hy hyI hyg hs
    rw [map_prod]
    let Jy : Ideal (MvPolynomial (Fin N) F) := RingHom.ker (aeval y : MvPolynomial (Fin N) F →ₐ[F] K)
    have hJy : I ⊔ Ideal.span {g} ≤ Jy := sup_le (fun a ha => (RingHom.mem_ker).2 (hyI a ha))
      ((Ideal.span_singleton_le_iff_mem _).2 ((RingHom.mem_ker).2 hyg))
    have : Jy.IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hPc : P ∈ projComponents (I ⊔ Ideal.span {g}) :=
      ⟨hPmin, i, fun h => hi (by simpa using (RingHom.mem_ker).1 (hPle h))⟩
    have hPf : P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset :=
      (Set.Finite.mem_toFinset _).2 hPc
    exact Finset.prod_eq_zero hPf (aeval_eq_zero_of_point (hf P hPf) s y hy
      (fun a ha => (RingHom.mem_ker).1 (hPle ha)) hs)

end GlobalTheory.HSElim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGenerated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hch := GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut k X hp (GlobalTheory.structureModule X) B (lbPow L m) hB.isLB (isLB_lbPow hL.isLB m)
    s t hs ht m (lbPow M m) (isLB_lbPow hM m) hcl
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPos
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.AmplePos

theorem pos_of_bound {h : ℕ → ℕ} {d C m₀ : ℕ} {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hf : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ h m)
    (hb : ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d| ≤
      C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) : 0 < a := by
  by_contra ha
  rw [not_lt] at ha
  obtain ⟨m, hm1, hm2⟩ := (hf.and_eventually (eventually_ge_atTop
    (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm2
  have hm1' : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  have hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m := by
    have h1 := Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))
    have h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hmK'
    push_cast at h2
    linarith
  have hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
    have h3 := (abs_le.mp (hb m hmm₀)).2
    have h4 : a * (m : ℤ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (by positivity)
    linarith
  have hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1)) := by
    have h5 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h5
    exact h5
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one] at hreal hm1
    linarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hreal hmK
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
    have h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) e
    have hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c := mul_pos hF hc
    rw [div_lt_iff₀ hFc] at hmK
    have h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤
        (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hF.le
    have hCpos : (0 : ℝ) ≤ C := by positivity
    have h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤
        (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hme : (0 : ℝ) < (m : ℝ) ^ e := by positivity
    have h8 := mul_lt_mul_of_pos_right hmK hme
    have h9 : (m : ℝ) ^ (e + 1) = m * m ^ e := by ring
    rw [h9] at h6
    nlinarith [h6, hreal, h7, h8]

theorem topSelf_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) →
    ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  intro k _ _ X _ _ hp d hd A hA
  obtain ⟨D, hD, c, hc, hf⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDd : D = d := by
    rw [hD] at hd
    exact_mod_cast hd
  subst hDd
  have hsupp : suppDim (structureModule X) ≤ (D : ℕ) := by
    unfold GlobalTheory.QCoh.suppDim
    rw [← hD]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨C, m₀, hb⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA
  rw [topSelf_def]
  exact pos_of_bound hc hf hb

end GlobalTheory.AmplePos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicExtremalNegativeFirstStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphic_extremal_negative_first : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q))) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (fun g => starRingEnd ℂ (T v g)) := by
  first | exact @GlobalTheory.HolRead.conj_extVec_isHolFor | exact GlobalTheory.HolRead.conj_extVec_isHolFor | (intros; apply GlobalTheory.HolRead.conj_extVec_isHolFor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.LieVB

variable {O : Type} [CommRing O]

theorem surjective_sec_epsZero : Function.Surjective (sec (epsZero O)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O O).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (DualNumber O)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O O).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (DualNumber O)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem appLE_sec_epsZero_epsFn {V : (Sp O).Opens} {T : (specO O (DualNumber O)).left.Opens}
    (h : V ≤ sec (epsZero O) ⁻¹ᵁ T) :
    (sec (epsZero O)).appLE T V h (resG _ le_top (epsFn O)) = 0 := by
  have e : (sec (epsZero O)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn O) = 0 :=
    congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans
      (map_zero (Scheme.ΓSpecIso (.of O)).inv.hom)
  rw [GlobalTheory.DualPull.appLE_resG, ← GlobalTheory.DualPull.resG_appLE _ le_top (le_preimage_top _ _), e,
    map_zero]

variable {G : Over (Sp O)} [GrpObj G]

theorem sec_epsZero_comp (x : LieG G) : sec (epsZero O) ≫ x.1.left = unitSec G :=
  congrArg (·.left) (epsZero_comp x)

theorem preimage_le_of_lieG (x : LieG G) {U : (Sp O).Opens} {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) : (specO O (DualNumber O)).hom ⁻¹ᵁ U ≤ x.1.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero O) ≫ (specO O (DualNumber O)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := h h₁
  rw [← sec_epsZero_comp x] at h₂
  exact h₂

theorem appLE_lieG (x : LieG G) {U : (Sp O).Opens} (hU : IsAffineOpen U) {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) :
    x.1.left.appLE W _ (preimage_le_of_lieG x h) f =
      (specO O (DualNumber O)).hom.appLE U _ le_rfl ((unitSec G).appLE W U h f) +
        (specO O (DualNumber O)).hom.appLE U _ le_rfl
          (GlobalTheory.VB.dualApp (tangent x) le_top (dUnit G h f)) * resG _ le_top (epsFn O) := by
  obtain ⟨⟨a, b⟩, e⟩ := (GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective O U hU).2 (x.1.left.appLE W _ (preimage_le_of_lieG x h) f)
  have hV : U ≤ sec (epsZero O) ⁻¹ᵁ (specO O (DualNumber O)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero O))).2 le_rfl
  have hb := dualApp_tangent_dUnit x h f hV le_rfl (preimage_le_of_lieG x h) a b e.symm
  have ha : (unitSec G).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero O)).appLE _ U hV) e
    simp only [map_add, map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      GlobalTheory.LB.resG_self, appLE_appLE (sec_epsZero_comp x) _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact e.symm

theorem tangent_injective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Injective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro x y hxy
  refine Subtype.ext (Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_))
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom (MonObj.one (X := G))) (V := ⊤)
    (x := (specO O (DualNumber O)).hom t) trivial
  have hT : IsAffineOpen ((specO O (DualNumber O)).hom ⁻¹ᵁ U) := c.affine_base.preimage _
  have e : x.1.left.appLE W _ (preimage_le_of_lieG x c.le) =
      y.1.left.appLE W _ (preimage_le_of_lieG y c.le) := by
    ext f
    exact (appLE_lieG x c.affine_base c.le f).trans
      (hxy ▸ (appLE_lieG y c.affine_base c.le f).symm)
  refine ⟨(specO O (DualNumber O)).hom ⁻¹ᵁ U, hU, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG x c.le),
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG y c.le), e]

end GlobalTheory.LieVB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMem
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TorFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def extZeroArch (w : InfinitePlace F) : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  ((LinearMap.inl F (Ainf F) (Af F)).comp (GlobalTheory.AutFunCompare.sgW w)).rTensor E

theorem compInf_extZeroArch_self (w : InfinitePlace F) (e : w.Completion ⊗[F] E) :
    compInf F E w (extZeroArch w e) = e := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW w (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_same]

theorem compInf_extZeroArch_ne {w u : InfinitePlace F} (h : u ≠ w) (e : w.Completion ⊗[F] E) :
    compInf F E u (extZeroArch w e) = 0 := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = 0
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

theorem compFin_extZeroArch (w : InfinitePlace F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (e : w.Completion ⊗[F] E) : compFin F E v (extZeroArch w e) = 0 := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0) ⊗ₜ[F] x = 0
    simp

theorem embArch_mem_unipRad_of_nilRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w),
    archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) →
    embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  intro F E _ _ _ _ _ σ hσ n J _ x w τ y hY
  classical
  set g := embArch σ J w y with hg
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J g).1 with hM
  set Y := archMat σ J τ y - 1 with hYdef
  set x' : Fin n → ℂ := fun i => τ.1 (x i) with hx'
  obtain ⟨hY1, hY2, hY3⟩ := mem_nilRad.1 hY

  have hinf : ∀ u, M.map (compInf F E u) = (matHom _ σ J (projArch σ J u g)).1 := fun u =>
    (congrArg Units.val (matHom_projArch σ J u g)).symm
  have hinf_ne : ∀ u, u ≠ w → M.map (compInf F E u) = 1 := fun u hu => by
    rw [hinf u, hg, projArch_embArch_ne σ J hu, map_one]; rfl
  have hfin : ∀ v, M.map (compFin F E v) = 1 := fun v => by
    have h := matHom_proj σ J v g
    rw [hg, proj_embArch, map_one] at h
    exact (congrArg Units.val h).symm
  let Φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hΦM : M.map Φ = archMat σ J τ y := by
    rw [GlobalTheory.Orb.archMat_apply, ← projArch_embArch_self σ J w y, ← hg, ← hinf w, Matrix.map_map]; rfl
  have hΦi : ∀ e : E, Φ (inclR (F := F) (AF F) e) = τ.1 e := fun e => by
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]

  have key : ∀ z : AF F ⊗[F] E, (∀ u, u ≠ w → compInf F E u z = 0) → (∀ v, compFin F E v z = 0) → Φ z = 0 → z = 0 :=
    fun z h1 h2 h3 => GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by
      by_cases hu : u = w
      · subst hu
        rw [map_zero]
        exact (infEmb_bijective hσ τ).1 (h3.trans (map_zero _).symm)
      · rw [h1 u hu, map_zero]) fun v => by rw [h2 v, map_zero]
  set m := M - 1 with hm
  have hmap : ∀ {R : Type} [CommRing R] (ψ : AF F ⊗[F] E →+* R), m.map ψ = M.map ψ - 1 := fun ψ => by
    change ψ.mapMatrix (M - 1) = _
    rw [map_sub, map_one]; rfl
  have hm_ne : ∀ u, u ≠ w → m.map (compInf F E u) = 0 := fun u hu => by rw [hmap, hinf_ne u hu, sub_self]
  have hm_fin : ∀ v, m.map (compFin F E v) = 0 := fun v => by rw [hmap, hfin v, sub_self]
  have hmΦ : m.map Φ = Y := by rw [hmap, hΦM]
  have hCΦ : (adMat F (Matrix.of fun i (_ : Fin 1) => x i)).map Φ = Matrix.of fun i (_ : Fin 1) => x' i := by
    ext i j; exact hΦi (x i)
  have hrow : ∀ k i, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J).map τ.1 k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    simp only [Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.of_apply, map_sum,
      map_mul, Matrix.vecMul, dotProduct, Pi.star_apply, hx']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show ((σ : E →+* E) (x l)) = σ (x l) from rfl, hσ.2.2.2]
  have hRΦ : ∀ k i, (adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J)).map Φ k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    rw [← hrow k i]; exact hΦi _
  refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
  · ext i j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, hCΦ]
      have := congrFun hY1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · ext k j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, Matrix.mul_apply]
      simp only [hRΦ]
      have := congrFun hY2 j
      simpa [Matrix.vecMul, dotProduct] using this
  · intro v hv
    have hv' : (star x' ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (v i)) = 0 := by
      have h0 := congrArg τ.1 (congrFun hv 0)
      rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at h0
      rw [← h0]
      simp only [Matrix.mulVec, dotProduct, hrow, Function.comp_apply]
    obtain ⟨c, hc⟩ := hY3 _ hv'
    obtain ⟨e, he⟩ := (infEmb_bijective hσ τ).2 c
    refine ⟨fun _ => extZeroArch w e, funext fun i => sub_eq_zero.1 (key _ (fun u hu => ?_) (fun v' => ?_) ?_)⟩
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_ne u hu, Matrix.zero_mulVec,
        show (compInf F E u ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compInf_extZeroArch_ne hu e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_fin v', Matrix.zero_mulVec,
        show (compFin F E v' ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compFin_extZeroArch w v' e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hmΦ, hCΦ]
      have hΦe : Φ (extZeroArch w e) = c := by
        change infEmb τ (compInf F E w (extZeroArch w e)) = c
        rw [compInf_extZeroArch_self, he]
      have h1 : (Φ ∘ fun j => inclR (F := F) (AF F) (v j)) = fun j => τ.1 (v j) := funext fun j => hΦi (v j)
      rw [h1, hc]
      simp [Matrix.mulVec, dotProduct, hΦe, mul_comm]

end GlobalTheory.TorFin
end
end

