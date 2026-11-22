import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem detId_stdL (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : Th.detId H (Th.stdL H N) M = detSub M := by
  classical
  unfold Th.detId detSub
  congr 1
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun j i => A i j, fun j => ?_, (Matrix.det_transpose A).symm⟩
    have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Matrix.of x).transpose, fun v hv => ?_, (Matrix.det_transpose _).symm⟩
    choose b hb using fun i => Submodule.mem_one.1 (hv i trivial)
    have e : (Matrix.of x).transpose.mulVec v = ∑ i, b i • x i := by
      funext j
      rw [Finset.sum_apply]
      show ∑ i, x i j * v i = ∑ i, b i • x i j
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hb, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

theorem ordSub_detSub_stdL (N : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) : ordSub w (detSub (Th.stdL H N)) = 0 := by
  rw [← detId_stdL, detId_std, Submodule.one_eq_span]
  have h := ordSub_span_singleton w (1 : H.Eˣ)
  rw [Units.val_one] at h
  rw [h]
  simp [ordF]

theorem tildeD_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsChiPsi H χ → ∀ (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)), Submodule.IsLattice H.E M → ∀ x : DtT H, (QuotientGroup.mk x : DtT H ⧸ UOT H) = relDetT H N (Th.stdL H N) M → ((tildeD H χ x : ℂˣ) : ℂ) = chiId χ (Th.detId H (Th.stdL H N) M) := by
  intro R H χ hχ N M hM x hx
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v y hy _ => hχ.unr v y hy) fun v _ => hχ.unr v
  have hU := (ChiLaws.chi_laws R H χ hχ).1
  have hfin := (ordSub_detSub_lattice H.E N M hM.fg hM.span_eq_top).1
  unfold relDetT at hx
  have h1 := hU _ (QuotientGroup.eq.1 hx)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1, tildeD_mk H hK, detId_stdL]
  unfold chiId
  congr 1
  simp only [ordSub_detSub_stdL, sub_zero]
  have h2 : Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 H.E) =>
      localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M)).toNat := by
    refine hfin.subset fun w hw h0 => hw ?_
    simp only [h0, Int.toNat_zero, pow_zero]
  refine ((χ.1.comp (finPartI H.E)).map_finprod h2).trans (finprod_congr fun w => ?_)
  rw [map_pow, MonoidHom.comp_apply, KerDet.finPartI_localIdele]
  rfl

end GlobalTheory.Mem.ChiDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpand
section
open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]
  simp_rw [hb, map_sum, map_smul]
  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]
    simp [map_sum, smul_eq_C_mul]
  rw [h2, map_sum]
  simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
    map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Mem.Col2.T_notMem_QE : ∀ {X : _root_.Formalism.L2.Col.Fields} {Pr : _root_.Formalism.L2.Col.Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : _root_.Formalism.L2.DIV.Tup X.F X.E X.K S) (u : Pr.Word), Pr.Ok → _root_.Formalism.L2.Col.IsSel X sel → Pr.T u ∈ S →
      ∀ w ∈ _root_.Formalism.L2.Col.QE sel (mu : _root_.Formalism.L2.DIV.Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro X Pr sel S mu u hOk hsel hT w hw hmem
  unfold _root_.Formalism.L2.Col.QE at hw
  split_ifs at hw with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hv
    have hmu := mu.2
    unfold _root_.Formalism.L2.DIV.tupGrp at hmu
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hmu
    have hA : _root_.Formalism.L2.DIV.GoodPl X.E S v := by
      by_contra hA
      exact hv (hmu.2 v hA)
    have hchar : _root_.Formalism.EigenvalueLevelCeiling.plc v ∉ S := by
      unfold _root_.Formalism.L2.DIV.GoodPl at hA
      exact hA.2.2
    have hv' : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← hsel v, Ideal.mem_comap]
      simpa using hmem
    have hp := hOk.T_prime u
    have hzero : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv'
    have : Nontrivial (𝓞 X.F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have hdvd : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ Pr.T u := (ringChar.spec _ _).mp hzero
    have heq : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left CharP.ringChar_ne_one
    apply hchar
    unfold _root_.Formalism.EigenvalueLevelCeiling.plc
    rw [heq]
    exact hT
  · simp at hw

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.PsiFix

theorem norm_psi0_le {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : 1 ≤ u) :
    ‖GlobalTheoryTheory.psi0 χ u‖ ≤ u * (Real.log u + 1) := by
  have hl : 0 ≤ Real.log u := Real.log_nonneg hu
  unfold GlobalTheoryTheory.psi0
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (GlobalTheoryTheory.abelian₂ n : ℂ) * χ (n : ZMod q)‖ ≤ u * Real.log u := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖(GlobalTheoryTheory.abelian₂ n : ℂ) * χ (n : ZMod q)‖ ≤ Real.log u := by
      intro n hn
      have hn' := Finset.mem_Icc.1 hn
      have hnu : (n : ℝ) ≤ u := (Nat.cast_le.2 hn'.2).trans (Nat.floor_le (by linarith))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg
        _ ≤ Real.log n := by rw [mul_one]; exact vonMangoldt_le_log
        _ ≤ Real.log u := Real.log_le_log hn0 hnu
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) hl
  refine (add_le_add h1 (?_ : _ ≤ u)).trans (le_of_eq (by ring))
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · simp; linarith

theorem exists_re_le (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ s : ℝ, 1 ≤ s → Real.log (3 * q) ≤ s →
      ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ρ.re ≤ 1 - c / s := by
  obtain ⟨c0, hc0, hZ⟩ := hZ
  have hfin := (ZeroWindow.finite_and_one_le_zmult q χ 0 0).1
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ zerosIn χ 0 0, ρ.re ≤ 1 - δ := by
    rcases (zerosIn χ 0 0).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨ρ0, h0, hmax⟩ := Set.exists_max_image _ (fun ρ : ℂ => ρ.re) hfin h
      exact ⟨1 - ρ0.re, by linarith [h0.2.1], fun ρ hρ => by linarith [hmax ρ hρ]⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  refine ⟨min (min (c0 / 2) δ) 1, by positivity, min_le_right _ _, fun s hs hs' ρ hρ => ?_⟩
  have hm1 : min (min (c0 / 2) δ) 1 ≤ c0 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min (c0 / 2) δ) 1 ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hs0 : 0 < s := by linarith
  by_cases him : ρ.im = 0
  · have := hδ' ρ ⟨hρ.1, hρ.2.1, by simp [him], hρ.2.2.2⟩
    have h2 : min (min (c0 / 2) δ) 1 / s ≤ δ := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith
  · have hne : ρ ≠ 1 := by
      intro h; apply him; simp [h]
    have hnot : ¬ Formalism.ZeroFreeDirichlet.InRegion c0 q ρ := fun h => him (hZ q χ ρ h ⟨Or.inr hne, hρ.2.2.2⟩).2.2.1
    unfold Formalism.ZeroFreeDirichlet.InRegion at hnot
    push Not at hnot
    have hg : |ρ.im| ≤ Real.exp s := by simpa using hρ.2.2.1
    have he : 1 ≤ Real.exp s := Real.one_le_exp hs0.le
    have ha : 0 ≤ |ρ.im| := abs_nonneg _
    have hpos : 0 < Real.log (q * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
    have hle : Real.log (q * (|ρ.im| + 2)) ≤ 2 * s := by
      calc Real.log (q * (|ρ.im| + 2)) ≤ Real.log ((3 * q) * Real.exp s) :=
            Real.log_le_log (by positivity) (by nlinarith)
        _ = Real.log (3 * q) + s := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
        _ ≤ 2 * s := by linarith
    have h3 : min (min (c0 / 2) δ) 1 / s ≤ c0 / Real.log (q * (|ρ.im| + 2)) := by
      calc min (min (c0 / 2) δ) 1 / s ≤ (c0 / 2) / s := div_le_div_of_nonneg_right hm1 hs0.le
        _ = c0 / (2 * s) := by rw [div_div]
        _ ≤ _ := div_le_div_of_nonneg_left hc0.le hpos hle
    linarith

theorem zsumR_recip_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have h1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hT := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hT, zsumR_eq_sum_toFinset χ 0 T _ hT, zsumR_eq_sum_toFinset χ 0 1 _ h1]
  rw [← Finset.sum_filter_add_sum_filter_not hT.toFinset (fun ρ : ℂ => 1 < |ρ.im|), add_comm]
  refine add_le_add ?_ (le_of_eq ?_)
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro ρ hρ
    obtain ⟨ha, hb⟩ := Finset.mem_filter.1 hρ
    have ha' : ρ ∈ zerosIn χ 0 T := by simpa using ha
    simp only [Set.Finite.mem_toFinset]
    exact ⟨ha'.1, ha'.2.1, by simpa using hb, ha'.2.2.2⟩
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    split_ifs <;> simp

theorem norm_zsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T u B : ℝ)
    (hB : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ B) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ B * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hT := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hT, zsum, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have h := hB ρ (by simpa using hρ)
  rw [norm_mul, norm_div, Complex.norm_natCast]
  calc (zmult χ ρ : ℝ) * (‖(u : ℂ) ^ ρ‖ / ‖ρ‖) ≤ (zmult χ ρ : ℝ) * (B / ‖ρ‖) := by gcongr
    _ = _ := by ring

theorem large (h1 : ExplZeta) (h2 : ExplChi) (h3 : LogDerOne) (h4 : ZeroCount) (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ s : ℝ, 1 ≤ s → Real.log (3 * q) ≤ s →
      ‖GlobalTheoryTheory.psi0 χ (Real.exp (s ^ 2))‖ ≤ K * s ^ 4 * (Real.exp (s ^ 2) * Real.exp (-c * s)) := by
  obtain ⟨c, hc, hc1, hre⟩ := exists_re_le hZ q χ
  obtain ⟨C1, hC1⟩ := GlobalTheory.Mem.An.ExplUsed.explicit_formula_used h1 h2 h3
  obtain ⟨C2, hC2⟩ := zsumR_recip_le h4
  set A := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) with hA
  have hA0 : 0 ≤ A := by
    rw [hA, zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  refine ⟨|C1| * (9 + 2 + A) + (A + 4 * |C2|), c, by positivity, hc, fun s hs hs' => ?_⟩
  have hs0 : 0 < s := by linarith
  have hss : s ≤ s ^ 2 := by nlinarith
  have hT2 : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hTu : Real.exp s ≤ Real.exp (s ^ 2) := Real.exp_le_exp.2 hss
  have hlq : Real.log q ≤ s := (Real.log_le_log (by linarith) (by linarith)).trans hs'
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have e1 := hC1 q χ hχ _ _ hT2 hTu
  have e2 := (hC2 q χ hχ _ hT2).1
  set u := Real.exp (s ^ 2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  set E := u * Real.exp (-c * s) with hE
  have l1 : Real.log (q * u) = Real.log q + s ^ 2 := by
    rw [Real.log_mul (by positivity) hu0.ne', hu, Real.log_exp]
  have l2 : Real.log (q * u * Real.exp s) = Real.log q + s ^ 2 + s := by
    rw [Real.log_mul (by positivity) (by positivity), l1, Real.log_exp]
  have l3 : Real.log (q * Real.exp s) = Real.log q + s := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  rw [l1, l2, ← hA] at e1
  rw [l3] at e2
  have hE1 : u / Real.exp s ≤ E := by
    rw [hE, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le
  have hE2 : 1 ≤ E := le_trans (by rw [le_div_iff₀ (Real.exp_pos _)]; linarith) hE1
  have hB : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ E := by
    intro ρ hρ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hE, hu, ← Real.exp_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    calc s ^ 2 * ρ.re ≤ s ^ 2 * (1 - c / s) := mul_le_mul_of_nonneg_left (hre s hs hs' ρ hρ) (by positivity)
      _ = _ := by field_simp; ring
  have e3 := norm_zsum_le χ _ u E hB
  have e4 := zsumR_recip_split χ (Real.exp s)
  rw [← hA] at e4
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  have hs24 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have e5 : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ (A + 4 * |C2|) * s ^ 4 := by
    have a1 : C2 * (Real.log q + s) ^ 2 ≤ |C2| * (4 * s ^ 4) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _))
    have a2 : A ≤ A * s ^ 4 := le_mul_of_one_le_right hA0 hs4
    linarith
  have e6 : u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s + (Real.log q + s ^ 2) + A ≤
      (9 + 2 + A) * s ^ 4 * E := by
    have a1 : (Real.log q + s ^ 2 + s) ^ 2 ≤ 9 * s ^ 4 := by
      calc (Real.log q + s ^ 2 + s) ^ 2 ≤ (3 * s ^ 2) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ = _ := by ring
    have a2 : u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s ≤ 9 * s ^ 4 * E := by
      calc u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s
          = (Real.log q + s ^ 2 + s) ^ 2 * (u / Real.exp s) := by ring
        _ ≤ _ := mul_le_mul a1 hE1 (by positivity) (by positivity)
    have a3 : (2 + A) * s ^ 4 ≤ (2 + A) * s ^ 4 * E := le_mul_of_one_le_right (by positivity) hE2
    have a4 : A ≤ A * s ^ 4 := le_mul_of_one_le_right hA0 hs4
    linarith
  have e7 : C1 * (u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s + (Real.log q + s ^ 2) + A) ≤
      |C1| * ((9 + 2 + A) * s ^ 4 * E) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e6 (abs_nonneg _))
  have e8 : E * zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ E * ((A + 4 * |C2|) * s ^ 4) :=
    mul_le_mul_of_nonneg_left e5 (by linarith)
  have e9 := norm_sub_le (GlobalTheoryTheory.psi0 χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
    (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
  rw [add_sub_cancel_right] at e9
  linarith

end GlobalTheory.Mem.An.PsiFix

namespace GlobalTheory.Mem.An

theorem psi0_le_exp_neg_sqrt_log : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne →
    GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 2 ≤ u →
      ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  intro h1 h2 h3 h4 hZ q _ χ hχ
  obtain ⟨K, c, hK, hc, hl⟩ := PsiFix.large h1 h2 h3 h4 hZ q χ hχ
  set S := max 1 (Real.log (3 * q)) with hS
  refine ⟨K * (24 / (c / 2) ^ 4) + (S ^ 2 + 1) * Real.exp (c / 2 * S), c / 2, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log u) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = Real.log u := Real.sq_sqrt hlu
  have hF : 0 < u * Real.exp (-(c / 2) * s) := by positivity
  have hp1 : 0 ≤ K * (24 / (c / 2) ^ 4) := by positivity
  have hp2 : 0 ≤ (S ^ 2 + 1) * Real.exp (c / 2 * S) := by positivity
  rw [mul_assoc]
  rcases le_total S s with h | h
  · have e := hl s ((le_max_left _ _).trans h) ((le_max_right _ _).trans h)
    rw [hsq, Real.exp_log hu0] at e
    have a := Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4
    have a' : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [this, mul_pow] at a
      linarith
    refine e.trans ?_
    calc K * s ^ 4 * (u * Real.exp (-c * s))
        ≤ K * (24 / (c / 2) ^ 4 * Real.exp (c / 2 * s)) * (u * Real.exp (-c * s)) := by gcongr
      _ = K * (24 / (c / 2) ^ 4) * (u * (Real.exp (c / 2 * s) * Real.exp (-c * s))) := by ring
      _ = K * (24 / (c / 2) ^ 4) * (u * Real.exp (-(c / 2) * s)) := by
          rw [← Real.exp_add]; congr 3; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hF.le
  · refine (PsiFix.norm_psi0_le χ u (by linarith)).trans ?_
    have a1 : 1 ≤ Real.exp (c / 2 * S) * Real.exp (-(c / 2) * s) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have a2 : Real.log u + 1 ≤ S ^ 2 + 1 := by
      rw [← hsq]; nlinarith
    calc u * (Real.log u + 1) ≤ u * ((S ^ 2 + 1) * (Real.exp (c / 2 * S) * Real.exp (-(c / 2) * s))) :=
          mul_le_mul_of_nonneg_left (a2.trans (le_mul_of_one_le_right (by positivity) a1)) hu0.le
      _ = (S ^ 2 + 1) * Real.exp (c / 2 * S) * (u * Real.exp (-(c / 2) * s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hF.le

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocPStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodulePatchAtPrime_isLattice_locP : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → Submodule.IsLattice E (patchAt P A B) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  first | exact @GlobalTheory.InertExchange.patchAt_isLattice_locP | exact GlobalTheory.InertExchange.patchAt_isLattice_locP | (intros; apply GlobalTheory.InertExchange.patchAt_isLattice_locP <;> assumption)
end

