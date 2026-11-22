import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOne
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormDegOne

theorem normV_under_eq : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  intro K L _ _ _ _ _ w h
  classical
  set P := w.asIdeal with hP
  set Q := (w.under (𝓞 K)).asIdeal with hQ
  have hQP : Q = P.under (𝓞 K) := rfl
  have : P.IsPrime := w.isPrime
  have : Q.IsPrime := (w.under (𝓞 K)).isPrime
  have hlo : P.LiesOver Q := ⟨hQP⟩
  have htow := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [h] at htow
  have hQ1 : Q.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_right htow.symm
  have hunder : Q.under ℤ = P.under ℤ := by rw [hQP, Ideal.under_under]
  have e1 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have : Q.LiesOver (P.under ℤ) := ⟨hunder.symm⟩
  have e2 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) Q
  rw [h, pow_one] at e1
  rw [hQ1, pow_one] at e2
  change Nat.card (𝓞 K ⧸ Q) = Nat.card (𝓞 L ⧸ P)
  change Ideal.absNorm Q = Ideal.absNorm P
  rw [← e1, ← e2]

end GlobalTheory.NormDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqSelfOfGoodChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmSelf

theorem not_mem_placesOver_of_normV {D : D7} {l M : ℕ} (hM : 0 < M) {P : Pl D.host.E}
    (h : normV P % (2 * l ^ M) = 1) : P ∉ placesOver D.host.E l := by
  intro hl
  have hmem : ((normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hl' : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
  have hdm := Nat.div_add_mod (normV P) (2 * l ^ M)
  rw [h] at hdm
  have hx : ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    push_cast
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
    rw [hk, pow_succ]
    exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_left _ hl'))
  have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have : (1 : 𝓞 D.host.E) = ((normV P : ℕ) : 𝓞 D.host.E) - ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) := by
      generalize normV P / (2 * l ^ M) = q at hdm ⊢
      rw [← hdm]
      push_cast; ring
    rw [this]
    exact P.asIdeal.sub_mem hmem hx
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory.AdmSelf

namespace GlobalTheory.AdmSelf

theorem admissibleConjugatePairPlaces_eq_self_of_goodChar : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ)
    (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))),
    (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) →
    (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X i M Q d hs hc hg hl
  classical
  have hnl : ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i) := fun P hP =>
    hl.elim (fun hM => not_mem_placesOver_of_normV hM (hg P hP).2) fun h => h P hP
  have hchar : ∀ P ∈ Q, ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)),
      IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
      (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
      (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P hP => by
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hg P hP
    refine ⟨d P, h1, h2, h3, fun w a c => h4 w (fun t => t.elim a c), fun A hA x => ?_⟩
    obtain ⟨σ, hσ, hx⟩ := h5 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun P hP => ?_
  obtain ⟨P', hPP'⟩ := GlobalTheory.TwistDet.exists_isConjPl P
  have hP' : P' ∈ Q := hc P hP P' hPP'
  refine mem_admissibleConjugatePairPlaces_iff.2 ⟨hP, P', hP', hPP', fun w hw => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hs _ hP, hnl _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨hs _ hP', hnl _ hP'⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨⟨P', by simp, hPP'⟩, hchar _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨⟨P, by simp, GlobalTheory.GalChar.isConjPl_symm hPP'⟩, hchar _ hP'⟩

end GlobalTheory.AdmSelf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitarisable_of_isLocComp (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, ⟨hV, hS⟩, -⟩ := (H E a ha).2.1 a 1 P (one_mul a) hP
  have hc := (H E a ha).2.2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem baseChange_speh_of_discreteSeries (H : GlobalTheory.Published.DiscreteSpectrumGL)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    GlobalTheory.DiscSpec.isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact GlobalTheory.T.satakeParameter_spherical_product_spehQuotients E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

end GlobalTheory.BcSpehProof

theorem GlobalTheory.BcSpeh.bcSpeh_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL → BcSpeh := by
  intro H1 H2 E _ _ _ hE n hn π hπ
  obtain ⟨c, N, h, V, σ, m, bc⟩ := H1 E hE n hn π hπ
  choose a d P _ hPn hPs using fun i => (H2 E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  exact GlobalTheory.BcSpehProof.baseChange_speh_of_discreteSeries H2 GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary hn hπ bc a d P hPn hPs fun i => (hPs i).mul_eq.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockType

theorem blockChar_eventually_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  intro k _ _ _ _ r t χ hχ
  have hval : Topology.IsOpenEmbedding (Units.val : kˣ → k) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hV : IsOpen ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)) := hval.isOpenMap _ hχ
  have hd : Continuous fun g : GL (Fin (r + t)) k =>
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det :=
    (Units.continuous_val.matrix_submatrix _ _).matrix_det
  refine ⟨(fun g : GL (Fin (r + t)) k => (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ⁻¹'
      ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)), hV.preimage hd, ?_, ?_⟩
  · refine ⟨1, χ.ker.one_mem, ?_⟩
    simp only [Units.val_one]
    rw [Matrix.submatrix_one _ (Fin.natAdd_injective t r), Matrix.det_one]
  · rintro g ⟨u, hu, he⟩
    rw [blockChar_eq χ g u he, MonoidHom.mem_ker.1 hu, Units.val_one]

end GlobalTheory.BlockType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.ChoiceAdm

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem star_eq_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

abbrev cnj (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem cnj_coe (x : 𝓞 D.host.E) : ((cnj D x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := rfl

theorem isConjPl_of_lev {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : IsConjPl D.host P P' := by
  have hle : P.asIdeal ≤ P'.asIdeal.comap (cnj D) := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : cnj D c = c' := RingOfIntegers.ext (by rw [cnj_coe, h2, star_eq_conj])
    rw [Ideal.mem_comap, e]
    exact h1
  have heq := P.isMaximal.eq_of_le (Ideal.comap_ne_top _ P'.isPrime.ne_top) hle
  intro x y hxy
  have e : y = cnj D x := RingOfIntegers.ext hxy
  rw [e, ← Ideal.mem_comap, ← heq]

theorem not_lev_self {P : Pl D.host.E} (h : IsSplitPl D.host P) : ¬ Lev.IsConjPl P P := fun hc =>
  GlobalTheory.SeriesTie.ne_of_split h (isConjPl_of_lev hc) rfl

theorem exists_idem {P : Pl D.host.E} (h : IsSplitPl D.host P) : ∃ e, IsIdemAt e P := by
  refine GlobalTheory.MovedIdem.exists_isIdemAt P fun hP => ?_
  obtain ⟨x, hx, hy⟩ := h
  refine hy (cnj D x) rfl ?_
  rw [← hP]
  exact Ideal.subset_span ⟨x, hx, by
    change ((cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)
    rw [cnj_coe, star_eq_conj]⟩

theorem lev_of_eq_cA {i j : Pl D.host.E} {a b : Formalism.L2.Theta.AE D} (ha : IsIdemAt a i) (hb : IsIdemAt b j)
    (e : a = cA D b) : Lev.IsConjPl j i := by
  have hc : Lev.IsConjPl j (GlobalTheory.IdemSupport.cP j) := fun c hc =>
    ⟨GlobalTheory.IdemSupport.cO D c, by
      show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) ∈ j.asIdeal
      rwa [show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) = c from RingOfIntegers.ext (star_star (c : D.host.E))], rfl⟩
  have h2 : IsIdemAt (cA D b) (GlobalTheory.IdemSupport.cP j) :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 j _ b hb hc
  rw [← e] at h2
  have hij : i = GlobalTheory.IdemSupport.cP j := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [ha.2 x hx, h2.2 x hx]
  rw [hij]
  exact hc

open Classical in
theorem splitSet_union {P H : Finset (Pl D.host.E)} (hP : SplitSet P) (hH : ∀ p ∈ H, ∃ e, IsIdemAt e p)
    (hc : ∀ p ∈ P ∪ H, ∀ p' ∈ P ∪ H, p ∈ H ∨ p' ∈ H → ¬ Lev.IsConjPl p p') : SplitSet (P ∪ H) := by
  classical
  have hid : ∀ p ∈ P ∪ H, IsIdemAt (idemAt p) p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hP.isIdemAt h
    · obtain ⟨e, he⟩ := hH p h
      rw [idemAt_eq he]
      exact he
  refine ⟨idem (P ∪ H), ⟨idemAt, hid, rfl⟩, ?_⟩
  rw [idem, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  by_cases hh : i ∈ H ∨ j ∈ H
  · rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hid i hi).1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hid j hj).1) with e | e
    · exact absurd (lev_of_eq_cA (hid i hi) (hid j hj) e) (hc j hj i hi hh.symm)
    · exact e
  · push_neg at hh
    have hi' : i ∈ P := (Finset.mem_union.1 hi).resolve_right hh.1
    have hj' : j ∈ P := (Finset.mem_union.1 hj).resolve_right hh.2
    exact hP.mul_conj hi' hj'

end GlobalTheory.ChoiceAdm

end

namespace GlobalTheory.ChoiceAdm

open Classical in

theorem adm_half_of_good_of_split_disjoint : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) →
      Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  intro D N X ρ hρ i j b Q hsplit hdisj
  classical
  have hG := hρ.base i j b
  have hdeQ : (ρ.B i j b).de.Q = half (ρ.ch i) (X.pD i) := by rw [hρ.delta i j b]; rfl
  have deS0 : ∀ P ∈ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP => by
    rw [hdeQ] at hP
    exact X.primes_subset_exceptional i (mem_half.1 hP).1
  have PgS0 : ∀ P ∈ (ρ.B i j b).G.Pg, P ∈ X.S0 i := fun P hP => by
    obtain ⟨k, hk⟩ := hρ.Pg i j b P hP
    exact Finset.mem_coe.1 (X.placesOver_subset_exceptional i k hk)
  have hH : ∀ P ∈ half (ρ.ch i) Q, P ∉ X.S0 i := fun P hP h =>
    Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 h

  have hcS0 : ∀ P ∈ half (ρ.ch i) Q, ∀ P' ∈ X.S0 i, ¬ Lev.IsConjPl P P' ∧ ¬ Lev.IsConjPl P' P := by
    intro P hP P' hP'
    refine ⟨fun hc => hH P hP ?_, fun hc => hH P hP ?_⟩
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (GlobalTheory.GalChar.isConjPl_symm (isConjPl_of_lev hc))
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (isConjPl_of_lev hc)
  have hA : ∀ P ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP =>
    (Finset.mem_union.1 hP).elim (PgS0 P) (deS0 P)
  refine ⟨⟨⟨(ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q ∪ half (ρ.ch i) Q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right
  · refine splitSet_union ?_ (fun p hp => exists_idem (hsplit p (mem_half.1 hp).1)) ?_
    · obtain ⟨P0, h1, h2, h3⟩ := hG.places.split
      exact h3.mono (Finset.union_subset h1 h2)
    · intro p hp p' hp' hh hc
      by_cases h1 : p ∈ half (ρ.ch i) Q
      · by_cases h2 : p' ∈ half (ρ.ch i) Q
        · by_cases e : p = p'
          · subst e
            exact not_lev_self (hsplit p (mem_half.1 h1).1) hc
          · exact ((hρ.ch i).pair p p' (isConjPl_of_lev hc) e).1 (mem_half.1 h1).2 (mem_half.1 h2).2
        · have : p' ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp').resolve_right h2
          exact (hcS0 p h1 p' (hA p' this)).1 hc
      · have hpA : p ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp).resolve_right h1
        have h2 : p' ∈ half (ρ.ch i) Q := hh.resolve_left h1
        exact (hcS0 p' h2 p (hA p hpA)).2 hc
  · refine Finset.disjoint_union_right.2 ⟨hG.places.disj, Finset.disjoint_left.2 fun p hp hq => hH p hq (PgS0 p hp)⟩
  · intro PP hPP PP' hPP'
    rcases hPP with h | h
    · exact hG.places.prime PP (Or.inl h) PP' hPP'
    · rcases Finset.mem_union.1 h with h | h
      · exact hG.places.prime PP (Or.inr h) PP' hPP'
      · refine hρ.goodSetup_count_eq_zero_off_badPlaces i PP' fun hS => ?_
        rcases hPP' with e | hc
        · exact hH PP h (e ▸ hS)
        · exact (hcS0 PP h PP' hS).1 hc
  · exact Finset.disjoint_left.2 fun p hp hq => hH p hq (deS0 p hp)

end GlobalTheory.ChoiceAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

open MvPolynomial Matrix

theorem eq_zero_of_coefFn_id_eq_zero (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
    (hF : ∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) : F = 0 := by
  classical
  set d : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)).det with hd
  have hev : ∀ v : D.what₂.Tau × Fin n × Fin n → ℂ, eval v d = ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det := by
    intro v
    rw [hd, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, eval_X]
  have hd0 : d ≠ 0 := by
    intro h
    have := hev (fun w => (1 : Matrix (Fin n) (Fin n) ℂ) w.2.1 w.2.2)
    rw [h, map_zero] at this
    have h1 : ∀ τ : D.what₂.Tau, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := by
      intro τ
      have : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
      rw [this, det_one]
    rw [Finset.prod_eq_one fun τ _ => h1 τ] at this
    exact zero_ne_one this
  have hFd : F * d = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det = 0
    · rw [h, mul_zero]
    · have hτ : ∀ τ, (Matrix.of fun a b => v (τ, a, b)).det ≠ 0 := fun τ hτ =>
        h (Finset.prod_eq_zero (Finset.mem_univ τ) hτ)
      let x : GLR D n := fun τ => GeneralLinearGroup.mkOfDetNeZero _ (hτ τ)
      have hx := hF x
      rw [coefFn] at hx
      have hu : ((detFam (fun τ => (lam τ).detShift) x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := (mul_eq_zero.mp hx).resolve_left hu
      have h3 : (fun w : D.what₂.Tau × Fin n × Fin n => (x w.1).val w.2.1 w.2.2) = v := by
        funext w
        rfl
      rw [h3] at h2
      have h4 : eval v F = 0 := by
        rw [← h2]
        rfl
      rw [h4, zero_mul]
  exact (mul_eq_zero.mp hFd).resolve_right hd0

end GlobalTheory.ExportSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalizationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contains_after_localization : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := by
  first | exact @GlobalTheory.CoefDuty.MemberO.member_duties | exact GlobalTheory.CoefDuty.MemberO.member_duties | (intros; apply GlobalTheory.CoefDuty.MemberO.member_duties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMonoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_conjunction_mono : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (EvO A M C tup P₁ → EvO A M C tup P₂ → EvO A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → EvO A M C tup P₁ → EvO A M C tup P₂) ∧ (BuiltEx A M C tup → EvO A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → Built A M C tup big' L → Built A M C tup big L := by
  first | exact @GlobalTheory.CoefDuty.LargeRing.evO_laws | exact GlobalTheory.CoefDuty.LargeRing.evO_laws | (intros; apply GlobalTheory.CoefDuty.LargeRing.evO_laws <;> assumption)
end

