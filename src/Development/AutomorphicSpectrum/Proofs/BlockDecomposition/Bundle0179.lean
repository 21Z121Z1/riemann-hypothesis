import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0173
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0175
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TiltSequenceDeterminedBySharp
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem tilt_inj {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A)
    (ha : ∀ i, a (i + 1) ^ l = a i) (hb : ∀ i, b (i + 1) ^ l = b i)
    (hs : ∀ i, A.sharp (a i) = A.sharp (b i)) : a = b := by
  have hf : ∀ x y : A.A, (x - y) ^ l = x ^ l - y ^ l := fun x y => map_sub A.frob x y
  have key : ∀ j i, a i - b i = (a (i + j) - b (i + j)) ^ (l ^ j) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      rw [ih i, pow_succ' l j, pow_mul, hf, ← add_assoc, ha, hb]
  have hmem : ∀ j, a j - b j ∈ Ideal.span {A.pi} := by
    intro j
    rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, A.sharpMap_eq, A.sharpMap_eq,
      hs j, sub_self]
  have hdvd : ∀ i j, A.pi ^ j ∣ a i - b i := by
    intro i j
    have h1 : A.pi ∣ a (i + j) - b (i + j) := Ideal.mem_span_singleton.1 (hmem (i + j))
    rw [key j i]
    exact (pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)
  have hH : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  funext i
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (hdvd i n)

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedSumLimitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_sandwich_approximation : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) → Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum | exact GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_frobenius_filtration_compat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  first | exact @GlobalTheory.CompanionTheory.TwFil.tw_fil | exact GlobalTheory.CompanionTheory.TwFil.tw_fil | (intros; apply GlobalTheory.CompanionTheory.TwFil.tw_fil <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormulaStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem exists_lim_of_dvd {R : Type*} [CommRing R] (p : R) [IsAdicComplete (Ideal.span {p}) R]
    (g : ℕ → R) (hg : ∀ n, p ^ n ∣ g (n + 1) - g n) : ∃ y, ∀ n, p ^ n ∣ g n - y := by
  have chain : ∀ m k, p ^ m ∣ g (m + k) - g m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ m ∣ g (m + k + 1) - g (m + k) :=
        (pow_dvd_pow p (Nat.le_add_right m k)).trans (hg (m + k))
      have := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) g (fun {m n} hmn => by
    rw [smodEq_span_singleton_pow_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (dvd_sub_comm).1 (chain m k))
  exact ⟨L, fun n => (smodEq_span_singleton_pow_iff _ _ _ _).1 (hL n)⟩

theorem isAdicComplete_quotient {R : Type*} [CommRing R] (p ξ : R)
    [IsAdicComplete (Ideal.span {p}) R] (h : ∀ (n : ℕ) (x : R), p ^ n ∣ ξ * x → p ^ n ∣ x) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
  have hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ∀ n : ℕ, ∃ y z, a = ξ * y + p ^ n * z := by
      intro n
      have hd := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hx n)
      rw [sub_zero] at hd
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h0 : Ideal.Quotient.mk (Ideal.span {ξ}) (a - p ^ n * c') = 0 := by
        rw [map_sub, map_mul, map_pow, hc, sub_self]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact ⟨y, c', by linear_combination hy⟩
    choose y z hyz using h1
    have hy : ∀ n, p ^ n ∣ y (n + 1) - y n := fun n =>
      h n _ ⟨z n - p * z (n + 1), by linear_combination hyz n - hyz (n + 1)⟩
    obtain ⟨Y, hY⟩ := exists_lim_of_dvd p y hy
    have hz : a - ξ * Y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {p}) _ fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero]
      obtain ⟨c, hc⟩ := hY n
      exact ⟨ξ * c + z n, by linear_combination hyz n + ξ * hc⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨Y, sub_eq_zero.1 hz⟩)
  have hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun f hf => ?_⟩
    have step : ∀ (n : ℕ) (x : R), Ideal.Quotient.mk (Ideal.span {ξ}) x = f n →
        ∃ y, Ideal.Quotient.mk (Ideal.span {ξ}) y = f (n + 1) ∧ p ^ n ∣ y - x := by
      intro n x hx
      obtain ⟨c, hc⟩ := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hf (Nat.le_succ n))
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨x - p ^ n * c', ?_, ⟨-c', by ring⟩⟩
      rw [map_sub, map_mul, map_pow, hx, ← hc]
      ring
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (f 0)
    let G : ∀ n, {x : R // Ideal.Quotient.mk (Ideal.span {ξ}) x = f n} := fun n =>
      Nat.rec ⟨x0, hx0⟩ (fun n x => ⟨(step n x.1 x.2).choose, (step n x.1 x.2).choose_spec.1⟩) n
    have hG : ∀ n, p ^ n ∣ (G (n + 1)).1 - (G n).1 := fun n => (step n _ (G n).2).choose_spec.2
    obtain ⟨y, hy⟩ := exists_lim_of_dvd p (fun n => (G n).1) hG
    refine ⟨Ideal.Quotient.mk _ y, fun n => ?_⟩
    rw [smodEq_span_singleton_pow_iff]
    have := map_dvd (Ideal.Quotient.mk (Ideal.span {ξ})) (hy n)
    rwa [map_pow, map_sub, (G n).2] at this
  exact { hH, hP with }

theorem isAdicComplete_U : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  intro l _ A
  have hc := isAdicComplete_quotient (l : A.W) A.xi (fun n x hx =>
    Ideal.mem_span_singleton.1 ((GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.2 n x (Ideal.mem_span_singleton.2 hx)))
  have e : (l : A.U) = Ideal.Quotient.mk (Ideal.span {A.xi}) (l : A.W) := (map_natCast A.th l).symm
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.Untilt
end

