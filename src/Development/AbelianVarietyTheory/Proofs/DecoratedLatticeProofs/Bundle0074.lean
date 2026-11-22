import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardMatrixStepIndicesLeExp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.IndexCountS

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum GlobalTheory.IndexCount

theorem card_index_le_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H j hj
  obtain ⟨hvG, -, -, hprod, -⟩ := BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, -, hsh, hI, -⟩ := H
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), Formalism.L2.Col.qOf P ≠ 0 := fun P h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hgg : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have h1 : Fintype.card (I.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (N.R.f * N.Nm ^ 2) := by
    rcases j with _ | i
    · obtain ⟨b, hb⟩ := hI.zero_uniq
      exact (Fintype.card_le_one_iff.2 fun a a' => (hb a).trans (hb a').symm).trans (Nat.one_le_pow _ _ hgg)
    · set n := N.R.N (i + 1) + cOf N.R (i + 1) with hn
      haveI : ∀ P : rowSG Pr sel mu, Finite (𝓞 X.E ⧸ P.1.asIdeal) := fun P => finite_res P.1
      let φ : I.β (i + 1) → ∀ P : rowSG Pr sel mu, Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal := fun b P =>
        resMat P.1 (Formalism.L2.Col.qOf P.1) (scE (N.R.N (i + 1)) fun i => i + 1) (I.h (i + 1) b P)
      have hφ : Function.Injective φ := by
        intro b b' hbb
        refine hI.inj i (by omega) b b' fun P => ?_
        have hP := hvG P.1 P.2
        have s1 := hI.stabG _ b P hP
        have s2 := hI.stabG _ b' P hP
        unfold lamYat at s1 s2
        rw [if_pos hP] at s1 s2
        refine ⟨1, Subgroup.one_mem _, (I.h (i + 1) b P)⁻¹ * I.h (i + 1) b' P, ?_, by group⟩
        unfold Jat
        rw [if_pos hP, hsh, if_pos rfl]
        exact mem_JGsym_of_cong _ _ (hq _) _ _ _ _ _ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s1) s2)
          (cong_of_resMat_eq _ _ (hq _) (GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX.ok hPr P.1 hP) s1 s2 (congrFun hbb P))
      have h2 := Nat.card_le_card_of_injective φ hφ
      have h3 : ∀ P : rowSG Pr sel mu, Nat.card (Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal) = Formalism.L2.Col.qOf P.1 ^ (n * n) := fun P => by
        rw [Nat.card_fun, Nat.card_prod, Nat.card_fin]
        rfl
      rw [Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_congr rfl fun P _ => h3 P, Finset.prod_pow, hprod, ← pow_mul] at h2
      refine h2.trans (Nat.pow_le_pow_right hgg (Nat.mul_le_mul_left _ ?_))
      have h4 : n ≤ N.Nm := by
        rw [hn]
        unfold NumDatum.Nm Ranks.N cOf
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ N.R.m by omega)
        rw [hd]
        have : i + 1 + d - 1 - (i + 1) ≤ d := by omega
        nlinarith [Nat.zero_le (d * N.R.t)]
      rw [sq]
      exact Nat.mul_le_mul h4 h4
  rw [hg 0, hg 1] at h1
  have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
  have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
  have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
  have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
  have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
  have he : N.R.f * N.Nm ^ 2 ≤ N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  calc (Fintype.card (I.β j) : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (N.R.f * N.Nm ^ 2) := by exact_mod_cast h1
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * N.Nm ^ 2) := pow_le_pow_left₀ (by linarith) ggT _
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
    _ = Real.exp (1 * errUnit N (Pr.T u)) := by
      rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
      unfold errUnit
      push_cast
      ring

end GlobalTheory.Core.Ht2.IndexCountS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlace
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.NormSign

open scoped Classical

theorem ext_algebraMap {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (x : K) :
    InfinitePlace.Completion.extensionEmbedding v (algebraMap K v.Completion x) = v.embedding x :=
  InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm x)

theorem tendsto_completion_iff {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) {α : Type}
    {l : Filter α} (f : α → K) (c : v.Completion) :
    Tendsto (fun x => algebraMap K v.Completion (f x)) l (𝓝 c) ↔
      Tendsto (fun x => v.embedding (f x)) l (𝓝 (InfinitePlace.Completion.extensionEmbedding v c)) := by
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.isInducing.tendsto_nhds_iff]
  exact iff_of_eq (congrArg (fun g => Tendsto g l _) (funext fun x => ext_algebraMap v (f x)))

theorem mk_eq_mk_iff_of_isReal {K : Type} [Field K] [NumberField K] {j σ : K →+* ℂ}
    (hj : ComplexEmbedding.IsReal j) : InfinitePlace.mk σ = InfinitePlace.mk j ↔ σ = j := by
  rw [InfinitePlace.mk_eq_iff]
  refine ⟨fun h => h.elim id fun h => ?_, Or.inl⟩
  have e : ComplexEmbedding.conjugate j = j := ComplexEmbedding.isReal_iff.mp hj
  ext x
  have h1 := RingHom.congr_fun h x
  have h2 := RingHom.congr_fun e x
  rw [ComplexEmbedding.conjugate_coe_eq] at h1 h2
  calc σ x = starRingEnd ℂ (j x) := by rw [← h1, Complex.conj_conj]
    _ = j x := h2

theorem tendsto_embedding {K : Type} [Field K] [NumberField K] {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j)
    {l : Filter K}
    (hl : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1))) (σ : K →+* ℂ) :
    Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1)) := by
  have h := (tendsto_completion_iff (InfinitePlace.mk σ) id _).1 (hl (InfinitePlace.mk σ))
  have hc : InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
      (if InfinitePlace.mk σ = InfinitePlace.mk j then -1 else 1) = if σ = j then -1 else 1 := by
    by_cases hσ : σ = j
    · subst hσ; simp
    · rw [if_neg (fun e => hσ ((mk_eq_mk_iff_of_isReal hj).1 e)), if_neg hσ, map_one]
  rw [hc] at h
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e] at h; exact h
  · rw [e] at h
    have h' := (Complex.continuous_conj.tendsto _).comp h
    have hs : starRingEnd ℂ (if σ = j then -1 else 1) = if σ = j then -1 else 1 := by
      split_ifs <;> simp
    rw [hs] at h'
    refine h'.congr fun x => ?_
    simp [ComplexEmbedding.conjugate_coe_eq]

theorem tendsto_norm {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j) {l : Filter K}
    (hσ : ∀ σ : K →+* ℂ, Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1))) (u : InfinitePlace E) :
    Tendsto (fun x => u.embedding (Algebra.norm E x)) l
      (𝓝 (if u = InfinitePlace.mk (j.comp (algebraMap E K)) then -1 else 1)) := by
  letI : Algebra E ℂ := u.embedding.toAlgebra
  have hn : ∀ x : K, u.embedding (Algebra.norm E x) = ∏ σ : K →ₐ[E] ℂ, σ x :=
    fun x => Algebra.norm_eq_prod_embeddings E ℂ x
  simp_rw [hn]
  have hlim : Tendsto (fun x => ∏ σ : K →ₐ[E] ℂ, σ x) l
      (𝓝 (∏ σ : K →ₐ[E] ℂ, if (σ : K →+* ℂ) = j then (-1 : ℂ) else 1)) :=
    tendsto_finset_prod _ fun σ _ => hσ (σ : K →+* ℂ)
  convert hlim using 2
  by_cases hu : u = InfinitePlace.mk (j.comp (algebraMap E K))
  · have he : u.embedding = j.comp (algebraMap E K) := by
      rw [hu]; exact InfinitePlace.embedding_mk_eq_of_isReal (hj.comp _)
    let σ₀ : K →ₐ[E] ℂ := { toRingHom := j, commutes' := fun e => (RingHom.congr_fun he e).symm }
    have hiff : ∀ σ : K →ₐ[E] ℂ, (σ : K →+* ℂ) = j ↔ σ = σ₀ := fun σ =>
      ⟨fun h => AlgHom.coe_ringHom_injective h, fun h => by rw [h]; rfl⟩
    rw [if_pos hu, Finset.prod_congr rfl fun σ _ => if_congr (hiff σ) rfl rfl]
    simp
  · rw [if_neg hu]
    refine (Finset.prod_eq_one fun σ _ => if_neg fun h => hu ?_).symm
    have he : u.embedding = j.comp (algebraMap E K) := by
      ext e
      have := σ.commutes e
      rw [← h]
      exact this.symm
    rw [← he, InfinitePlace.mk_embedding]

end GlobalTheory.NormSign

namespace GlobalTheory.NormSign

open scoped Classical

theorem exists_norm_sign : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  intro E K _ _ _ _ _ j hj T M W hW
  set w₀ := InfinitePlace.mk (j.comp (algebraMap E K)) with hw₀

  let y : GlobalTheory.FrobDense.Loc T := (fun u => if u = InfinitePlace.mk j then -1 else 1, fun _ => 1)
  let f : K → GlobalTheory.FrobDense.Loc T := fun x => GlobalTheory.FrobDense.proj T (algebraMap K (AdeleRing (𝓞 K) K) x)
  let l : Filter K := comap f (𝓝 y)
  haveI : l.NeBot := comap_neBot_iff.2 fun t ht => by
    obtain ⟨_, hz, a, rfl⟩ := mem_closure_iff_nhds.1 (GlobalTheory.FrobDense.denseRange_proj T y) t ht
    exact ⟨a, hz⟩
  have hf : Tendsto f l (𝓝 y) := tendsto_comap
  have hinf : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1)) := fun u =>
    (((continuous_apply u).comp continuous_fst).tendsto y).comp hf
  have hfin : ∀ v : T, Tendsto (fun x => algebraMap K (v.1.adicCompletion K) x) l (𝓝 1) := fun v =>
    (((continuous_apply v).comp continuous_snd).tendsto y).comp hf
  have hσ := tendsto_embedding hj hinf

  have h0 : ∀ᶠ x in l, x ≠ 0 := by
    have hj' := hσ j
    rw [if_pos rfl] at hj'
    filter_upwards [hj'.eventually_ne (by norm_num : (-1 : ℂ) ≠ 0)] with x hx e
    exact hx (by rw [e, map_zero])

  have h1 : ∀ᶠ x in l, ∀ v : T, v.1.valuation K (x - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [eventually_all]
    intro v
    have ho : IsOpen {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} :=
      (GlobalTheory.Mem.UnitOpen.isOpen_val_le v.1 (-(M : ℤ))).preimage (continuous_sub_right 1)
    have hm : (1 : v.1.adicCompletion K) ∈ {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} := by
      show Valued.v ((1 : v.1.adicCompletion K) - 1) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    filter_upwards [hfin v (ho.mem_nhds hm)] with x hx
    have e : Valued.v (algebraMap K (v.1.adicCompletion K) x - 1) = v.1.valuation K (x - 1) := by
      rw [← map_one (algebraMap K (v.1.adicCompletion K)), ← map_sub]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 (x - 1)
    rw [← e]
    exact hx

  let Φ : (InfiniteAdeleRing E)ˣ →* Ideles E :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hΦ : Continuous Φ := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  let P := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w₀ (-1)
  let p : (InfiniteAdeleRing E)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) P
  have hP : Φ p = P := Units.ext rfl
  have hpW : Φ ⁻¹' W ∈ 𝓝 p := hΦ.continuousAt.preimage_mem_nhds (by rw [hP]; exact hW)
  rw [(GlobalTheory.HeckeGal.isOpenEmbedding_val_inf E).isInducing.nhds_eq_comap, mem_comap] at hpW
  obtain ⟨U, hU, hUW⟩ := hpW
  have hpu : ∀ u : InfinitePlace E, InfinitePlace.Completion.extensionEmbedding u ((p : InfiniteAdeleRing E) u) =
      if u = w₀ then -1 else 1 := by
    intro u
    by_cases hu : u = w₀
    · subst hu
      rw [if_pos rfl]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self]
      simp
    · rw [if_neg hu]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne E w₀ u hu, map_one]
  have hg : Tendsto (fun x => algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x)) l
      (𝓝 (p : InfiniteAdeleRing E)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have := (tendsto_completion_iff u (fun x => Algebra.norm E x) ((p : InfiniteAdeleRing E) u)).2
      (by rw [hpu u]; exact tendsto_norm hj hσ u)
    exact this
  have h2 : ∀ᶠ x in l, algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x) ∈ U := hg hU
  obtain ⟨x, ⟨hx0, hx1⟩, hx2⟩ := ((h0.and h1).and h2).exists
  refine ⟨Units.mk0 x hx0, fun w hw => hx1 ⟨w, hw⟩, ?_⟩
  let q : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom
    (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))
  have hq : Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E)
      (diagUnits E (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))) = Φ q := Units.ext rfl
  rw [hq]
  exact hUW (show (q : InfiniteAdeleRing E) ∈ U from hx2)

end GlobalTheory.NormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToL
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

open Formalism.L2.Th1 in

theorem mulBy_coefLe_of_kernel_prime_to :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  intro L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker
  have hβp : ι β ≠ 0 := by
    intro h
    rw [h, norm_zero] at hβ
    exact zero_ne_one hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, map_zero] at hβp
    exact hβp rfl
  have hW : E.IntCurve (E.curveL l L ι) := E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hΔ : (E.curveL l L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htwo := E.ScaledModelNorms.norm_two l hl
  have hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨S, hS⟩ := F.kerRepsExist L β hβ0 hst
  obtain ⟨neg, -, hE⟩ := F.endoZInstance L β S hβ0 hst hS
  have hb2 : (E.curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hEp := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
  rw [← E.wpBridge l L ι] at hEp
  have hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β) := by
    rw [hb2]
    simpa using hEp
  have hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    have := E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD)
      (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2
    simpa using this
  obtain ⟨hLP, hXW, hA, -, -⟩ := C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC
  have hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l] := by
    intro x hx
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv, hx, inv_one]
  have hM := A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1
    hC.2.2.2.2
  have key := C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι))
    (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι))
    ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ)))
    (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    (fun P : S => E.xT (E.curveL l L ι) (E.ptOf l L ι (P : ℂ))) (ι β)
    ((ι β)⁻¹ * ((Fintype.card S : ℂ_[l]) + 1)) hLP hXW hA (hinv _ htwo)
    ⟨hEp', by rw [← mul_assoc, mul_inv_cancel₀ hβp, one_mul], ?_, ?_, fun P => (hint P).1, hβ.le,
      hinv _ hβ, by rw [hb2, zero_div, mul_zero]; exact zero_mem _⟩
  · exact fun n => key n
  · intro P
    rw [hb2, zero_div, map_zero, add_zero]
    exact E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2
  · intro P n
    unfold E.xT
    beta_reduce
    rw [E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]
    refine (hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1
    show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
    rw [norm_div, htwo, div_one]
    exact (hint P).2

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLatticeMajorantStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muMaxDual_nonpos_of_dual_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (A : HLat K) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (e : (Fin n → K) ≃ₗ[K] A.V) (M : Submodule (𝓞 K) (Fin n → K)), A.Good → 0 < A.rank → (∀ i j, H i j ∈ K0) → (∀ (v : InfinitePlace K) (i j : Fin n), Formalism.HermitianLatticesTheory.majAt A.b A.X v (e (Pi.single i 1)) (e (Pi.single j 1)) = v.embedding (H i j)) → A.L = M.map (e.toLinearMap.restrictScalars (𝓞 K)) → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → A.muMaxDual ≤ 0 := by
  first | exact @GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord | exact GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord | (intros; apply GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactEntriesLeOne
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem continuous_lin_mvZ {T : Type} [TopologicalSpace T] (g : T → ι → Matrix (Fin a) (Fin a) ℂ)
    (hg : Continuous g) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, Continuous fun x => Λ (mvZ (g x) h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro Λ; simp only [mvZ, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro Λ; simp only [map_add]; exact (hp Λ).add (hq Λ)
  | mul_X p v hp =>
    intro Λ
    have key : ∀ x, Λ (mvZ (g x) h (p * X v)) = ∑ i, ∑ j, (h v.1 i v.2.1 * g x v.1 v.2.2 j) *
        (Λ ∘ₗ LinearMap.mulRight ℂ (X (v.1, i, j))) (mvZ (g x) h p) := by
      intro x
      rw [map_mul]
      conv_lhs => rw [show mvZ (g x) h (X v) = ∑ i, ∑ j, C (h v.1 i v.2.1 * g x v.1 v.2.2 j) * X (v.1, i, j) by simp [mvZ, aeval_X]]
      simp only [Finset.mul_sum, map_sum, LinearMap.comp_apply, LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [C_mul', mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [key]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    refine Continuous.mul (continuous_const.mul ?_) (hp _)
    exact ((continuous_apply j).comp ((continuous_apply v.2.2).comp ((continuous_apply v.1).comp hg)))

theorem continuous_evalAt_mul (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => evalAt (fun τ => u τ * y τ) F := by
  unfold evalAt
  refine (MvPolynomial.continuous_eval F).comp (continuous_pi fun x => ?_)
  exact (((continuous_apply x.1).matrix_mul continuous_const).matrix_elem x.2.1 x.2.2)

theorem isCompact_entries_le_one :
    IsCompact {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} := by
  have : {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} =
      Set.univ.pi fun _ : ι => (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Metric.closedBall (0:ℂ) 1 : Set (Matrix (Fin a) (Fin a) ℂ)) := by
    ext u
    constructor
    · intro hu τ _ i _ j _
      have := hu τ i j
      show dist (u τ i j) 0 ≤ 1
      simpa using this
    · intro hu τ i j
      have : dist (u τ i j) 0 ≤ 1 := hu τ trivial i trivial j trivial
      simpa using this
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem subY_eq_sum_averages : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ y' : ι → Matrix (Fin b) (Fin b) ℂ, ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → FP ι a b), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∑ j, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F ∂ν = Λ (subY hab y' F) := by
  intro ι _ a b hab lam n K _ _ _ _ _ ν _ r hr y'
  obtain ⟨m, y, P, hy, hT⟩ := GlobalTheory.T.exists_invertibleFamily_eval_span ι a lam n (FP ι a b) (subY hab y').toLinearMap
  refine ⟨m, y, P, hy, ?_⟩
  intro F hF Λ
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  have vn := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).2
  have hstar : ∀ k τ, star (r k τ) * r k τ = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff').1 (hr.uni k τ)
  have hstar' : ∀ k τ, r k τ * star (r k τ) = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff).1 (hr.uni k τ)
  have hinv : ∀ k τ, (r k τ)⁻¹ = star (r k τ) := fun k τ => Matrix.inv_eq_left_inv (hstar k τ)
  have hpt : ∀ k, ∑ j, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F
      = Λ (subY hab y' F) := by
    intro k
    have hG : subY hab y' (lft (r k) F) = ∑ j, evalAt (y j) (lft (r k) F) • P j := hT _ (vn (r k) F hF)
    have e1 : mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (subY hab y' (lft (r k) F)) = subY hab y' F := by
      rw [h1, h4]
      have ha : (fun τ => r k τ * (r k τ)⁻¹) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
        funext τ; rw [hinv, hstar']
      have hb : (fun τ => (1 : Matrix (Fin b) (Fin b) ℂ) * y' τ) = y' := by funext τ; simp
      rw [ha, hb, h5]
    rw [← e1, hG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, h6, mul_comm]
  have hst : Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ) := continuous_pi fun τ => (continuous_apply τ).star
  have hcont : ∀ j, Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
      Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F := fun j => by
    have e1 := continuous_lin_mvZ (fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ)) hst (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (P j) Λ
    exact e1.mul (continuous_evalAt_mul (y j) F)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) *
      evalAt (fun τ => r k τ * y j τ) F) ν := by
    intro j _
    have hfun : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F)
        = (fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
          Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F) ∘ r := by
      funext k; simp only [Function.comp_apply, hinv]
    rw [hfun]
    obtain ⟨C, hC⟩ := (isCompact_entries_le_one (ι := ι) (a := a)).exists_bound_of_continuousOn (hcont j).continuousOn
    refine Integrable.of_bound ((hcont j).comp hr.cont).aestronglyMeasurable C (Filter.Eventually.of_forall fun k => ?_)
    exact hC _ fun τ i i' => entry_norm_bound_of_unitary (hr.uni k τ) i i'
  rw [← integral_finset_sum _ hint]
  simp_rw [hpt]
  simp

end GlobalTheory.KJInf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlockStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  first | exact @GlobalTheory.ParHecke.isHgt_lower | exact GlobalTheory.ParHecke.isHgt_lower | (intros; apply GlobalTheory.ParHecke.isHgt_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMulStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ), genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  first | exact @GlobalTheory.ParHecke.genVal_map_mul | exact GlobalTheory.ParHecke.genVal_map_mul | (intros; apply GlobalTheory.ParHecke.genVal_map_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.AAUnitS

theorem aaUnit_bad_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h B P hP
  have hcond := h.1.pr_cond
  obtain ⟨⟨-, -, -, hcc, -, -, -, -, -, hPr, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  obtain ⟨l, hl, hlP, hd⟩ := GlobalTheory.ColNormsUnit.exists_prime hPr sel u P hP
  rw [hcond] at hd
  refine GlobalTheory.AAUnitAway.locP_AA D X s _ dl B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    exact hd (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  · rintro rfl
    exact hd ((dvd_mul_left _ _).mul_right _)
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.Core.Ht2.AAUnitS
end

