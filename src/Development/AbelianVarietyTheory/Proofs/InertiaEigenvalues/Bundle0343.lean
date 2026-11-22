import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTeichmullerOfFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesConjOfAdm
section
noncomputable section

namespace GlobalTheory.GoodTypes

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant
open scoped Classical

section Local

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {G V U : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U]

def ConjIn (ρ : Representation ℂ G V) (W : Submodule ℂ V) (j : Gn g n →* G)
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) U) : Prop :=
  ∀ y ∈ W, y ≠ 0 → ∃ Λ : V →ₛₗ[starRingEnd ℂ] U, Λ y ≠ 0 ∧
    ∀ z ∈ W, Λ z ∈ fixK1 π ∧ ∀ h, Λ (ρ (j h) z) = π (lift g n h) (Λ z)

def typeSpan {ι T : Type} (ρ : Representation ℂ G V) (b : ι → V) (ty : ι → T) (π : T) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (x : G) (σ : ι), ty σ = π ∧ z = ρ x (b σ)}

theorem ConjIn.act_ne {ρ : Representation ℂ G V} {W : Submodule ℂ V} {j : Gn g n →* G}
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) U} (h : ConjIn ρ W j π) (a a' : MonoidAlgebra ℂ (Gn g n))
    (ha : ∀ x, starRingEnd ℂ (a.coeff x) = a'.coeff x) {y : V} (hy : y ∈ W) (h0 : y ≠ 0)
    (hfix : ∑ x, a.coeff x • ρ (j x) y = y) : ∃ u ∈ fixK1 π, actK π a' u ≠ 0 := by
  obtain ⟨Λ, h1, h2⟩ := h y hy h0
  refine ⟨Λ y, (h2 y hy).1, ?_⟩
  have : actK π a' (Λ y) = Λ y := by
    conv_rhs => rw [← hfix]
    rw [map_sum, actK, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, map_smulₛₗ, ha, (h2 y hy).2]
  rwa [this]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (h : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod) : f = f' := by
  have h3 := congrArg Polynomial.roots h
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g), ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) (Multiset.map_injective hτ h3)

end Local

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroPrime (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def facHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Gn (D.host.g k) D.R.r →* G0g D.nd :=
  MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩

abbrev LocRep (D : D7) (k : Fin 2) : Type 1 := Rep.{0} ℂ (GL (Fin D.R.r) ℚ_[D.host.g k])

abbrev Corr (D : D7) : Type 1 := ∀ (k : Fin 2) (v : D.nd.PlG k), LocRep D k → D.naut.LP (D.naut.plGw k v)

abbrev Comp (D : D7) : Type 1 := D.what₂.FT → ∀ k : Fin 2, D.nd.PlG k → LocRep D k

def SeriesTame (D : D7) (rc : Corr D) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : LocRep D k), IsIrrRep π.ρ → GlobalTheory.SplitWeil.IsSmoothRep π.ρ →
    D.naut.lpDim (rc k v π) = D.R.r ∧
    ∀ f, (∃ u ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k f) u ≠ 0) →
      D.naut.inePol (rc k v π) (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod

def ParamTie (D : D7) (i : D.nd.Loc) (rc : Corr D) (cp : Comp D) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), IsIrrRep (cp σ k v).ρ ∧ GlobalTheory.SplitWeil.IsSmoothRep (cp σ k v).ρ ∧
    D.naut.locW i σ (D.naut.plGw k v) = rc k v (cp σ k v)

def SeriesConj (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f →
    (D.ntypes.eSer k f).coeff.mapRange (starRingAut : ℂ ≃+* ℂ) (map_zero _) =
      (D.ntypes.eSer k (labAct D starRingAut k f)).coeff

theorem labAct_conj (D : D7) (k : Fin 2) {f : (ZMod (D.host.g k))[X]} (hf : IsLabel D k f) :
    labAct D starRingAut k f = dualLab D k f := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Compare.TeichmullerRoots.dual_spec hf.1 hf.2.2
  refine GlobalTheory.Compare.TeichmullerRoots.labAct_eq D k _ (-1) (fun ζ hζ => ?_) hf h1 h2
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ
    (GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport.rootExp_ne_zero D.R.r _ (D.host.g_prime k).two_le)
  rw [zpow_neg_one, Complex.inv_eq_conj hn]
  rfl

theorem act_atPlace (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V)
    (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (y : V) :
    ρ.asAlgebraHom (atPlace D k v a) y = ∑ x, a.coeff x • ρ (facHom D k v x) y := by
  rw [GlobalTheory.SeriesSupportTest.atPlace_eq]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    have : GlobalTheory.SeriesSupportTest.plHom D k v (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (facHom D k v h) c := MonoidAlgebra.mapDomain_single
    rw [this, Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem exists_good (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) {x : V}
    (hx : x ≠ 0) (he : ρ.asAlgebraHom D.ntypes.e0 x = x) :
    ∃ (t : Tup2 D) (a : MonoidAlgebra ℂ (G0g D.nd)), D.ntypes.goodTuple t ∧ ρ.asAlgebraHom a x ≠ 0 ∧
      ∀ k v, ρ.asAlgebraHom (atPlace D k v (D.ntypes.eSer k (t k v))) (ρ.asAlgebraHom a x) = ρ.asAlgebraHom a x := by
  rw [Ten.e0_eq, Ten.eGood, map_sum, LinearMap.sum_apply] at he
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (he.trans_ne hx)
  by_cases hg : Ten.goodVec D p
  · rw [if_pos hg] at hp
    refine ⟨_, _, hg, hp, fun k v => ?_⟩
    rw [← Module.End.mul_apply, ← map_mul,
      ← Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D k v _ (D.ntypes.eSer_central k _)),
      Ten.atPlace_eq, Ten.tens_mul_plc]
    congr 3
    exact Function.update_eq_self_iff.2 (D.ntypes.eSer_idem _ _)
  · rw [if_neg hg] at hp
    simp at hp

variable {D : D7} {X : BaseLevelRowSide D}

def TypeTie (Y : Prov D X) (cp : Comp D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) (P : Pair D.what₂.LL (G0g D.nd))
    (j : S.RR.V →ₗ[D.what₂.LL] Y.sK.RR.V) {ι : Type} (b : ι → EE) (ty : ι → D.what₂.FT) : Prop :=
  ∃ (aE : EE →ₗ[ℂ] Y.EEK) (aA : ∀ μ, S.Amb μ →ₗ[ℂ] Y.sK.Amb μ), IsLevelIn Y S P j aE aA ∧
    ∀ σ k v, ConjIn Y.actEE (typeSpan Y.actEE (fun s => aE (b s)) ty σ) (facHom D k v) (cp σ k v).ρ

end GlobalTheory.GoodTypes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNeStatement
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  first | exact @GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | exact GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | (intros; apply GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLocalIff
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LocalSpanCriterion

theorem span_local_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module (RingOfIntegers K) V] (w : HeightOneSpectrum (RingOfIntegers K))
    [Module (Formalism.L2.Col.Ow w) V] [IsScalarTower (RingOfIntegers K) (Formalism.L2.Col.Ow w) V]
    (T : Set V) (x : V) :
    x ∈ Submodule.span (Formalism.L2.Col.Ow w) T ↔
      x ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) := by
  have hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) ↔
      ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T := fun y => Iff.rfl
  rw [hmem]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
      have e : (s * t) • (y + z) = t • (s • y) + s • (t • z) := by
        rw [smul_add, mul_smul, smul_comm s t y, mul_smul]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl a
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩
      have hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) *
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) =
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r := IsLocalization.mk'_spec _ r t
      simp only at hrt
      rw [hrt] at hspec
      have e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y) := by
        have ht : (t : RingOfIntegers K) • (a • y) = r • y := by
          rw [← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul,
            mul_comm, hspec, algebraMap_smul]
        rw [mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]
      rw [e]
      exact Submodule.smul_mem _ r hsy
  · rintro ⟨s, hs, hsx⟩
    have hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s) :=
      IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    have h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T := by
      have := Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx
      exact this
    rw [← algebraMap_smul (Formalism.L2.Col.Ow w) s x] at h1
    obtain ⟨u, hu'⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

end GlobalTheory.LocalSpanCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesisStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_two_of_galois_hypothesis : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanTwo i s := by
  first | exact @GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | exact GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | (intros; apply GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.SplitBelow

theorem ef_eq_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P)
    (hN : Ideal.absNorm P = p) : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 1 := by

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmZ : ((p : ℤ) : 𝓞 E) ∈ P := by simpa using hm
  have hU : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd P hP hmZ
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpZ).mpr hmZ
  have hf : P.inertiaDeg ℤ = 1 := by
    have h := Ideal.pow_inertiaDeg p P
    rw [hN] at h
    exact Nat.pow_right_injective hp.two_le (by simpa using h)
  have het := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 F)) P
  have hft := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 F)) P
  rw [he] at het
  rw [hf] at hft
  rw [(mul_eq_one.mp het.symm).2, (mul_eq_one.mp hft.symm).2]
  exact mul_one 1

theorem splits_below_of_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by

  intro E _ _ _ p hp hd hN P hPm
  classical
  by_contra hns
  have hO : ∀ Q : HeightOneSpectrum (𝓞 E), GlobalTheory.CMVal.Over Q (below P) → Q = P := by
    intro Q hQ
    by_contra hne
    exact hns ⟨Q, P, hne, hQ, over_below P⟩
  have hq1 : ∀ q : (below P).asIdeal.primesOver (𝓞 E), q.1 = P.asIdeal := by
    intro q
    have hq := q.2
    have := hq.1
    have := hq.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (below P).ne_bot q.1
    have h := hO ⟨q.1, hq.1, hne⟩ (Ideal.LiesOver.over (P := q.1) (p := (below P).asIdeal)).symm
    exact congrArg HeightOneSpectrum.asIdeal h
  have hterm : ∀ q : (below P).asIdeal.primesOver (𝓞 E),
      q.1.ramificationIdx (OF E) * q.1.inertiaDeg (OF E) = 1 := by
    intro q
    rw [hq1 q]
    have := P.isPrime
    exact ef_eq_one (maximalRealSubfield E) E hp hd P.asIdeal hPm (hN P hPm)
  have hfr : Module.finrank (OF E) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (OF E) (maximalRealSubfield E) (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (below P).asIdeal (𝓞 E)
  rw [Finset.sum_congr rfl (fun q _ => hterm q), hfr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hle : Fintype.card ((below P).asIdeal.primesOver (𝓞 E)) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext ((hq1 a).trans (hq1 b).symm))
  omega

end GlobalTheory.LamTie.SplitBelow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqMulNotMemMaximalIdealPowThreeMul
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open IsDiscreteValuationRing in

theorem sq_mul_not_mem_maxIdeal_pow :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ),
      p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c →
      ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  intro F _ _ _ _ p e c hp he hord hc w hw heq
  have hw' : w = (p : 𝒪[F]) ^ 2 * (c : 𝒪[F]) := by
    apply Subtype.ext
    simpa using heq

  have hcop : IsCoprime (p : ℤ) c :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hc
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom 𝒪[F])
  have h1 : IsUnit (a * (Int.castRingHom 𝒪[F]) p + b * (Int.castRingHom 𝒪[F]) c) := by
    rw [hab]; exact isUnit_one
  have hpnu : ¬ IsUnit (p : 𝒪[F]) := by
    rintro ⟨u, hu⟩
    have h0 := addVal_eq_zero_of_unit u
    rw [hu] at h0
    unfold OrdIs at hord
    rw [hord] at h0
    exact (Nat.pos_iff_ne_zero.mp he) (by exact_mod_cast h0)
  have hcu : IsUnit (c : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exfalso; apply hpnu
      have := isUnit_of_mul_isUnit_right h
      simpa using this
    · have := isUnit_of_mul_isUnit_right h
      simpa using this

  have hval : addVal 𝒪[F] w = ((2 * e : ℕ) : ℕ∞) := by
    obtain ⟨u, hu⟩ := hcu
    rw [hw', addVal_mul, addVal_pow, ← hu, addVal_eq_zero_of_unit, add_zero]
    unfold OrdIs at hord
    rw [hord]
    push_cast
    rfl
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[F]
  rw [(irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  have hle := (addVal_le_iff_dvd).mpr hw
  rw [addVal_pow, addVal_uniformizer hϖ, hval] at hle
  have : ((3 * e : ℕ) : ℕ∞) ≤ ((2 * e : ℕ) : ℕ∞) := by simpa using hle
  have := ENat.coe_le_coe.mp this
  omega

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAllStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_J_all : ∀ D : D7, AdmissibleParameterJ.JumpBoundClosedForm D := by
  first | exact @GlobalTheory.JumpStatement.holds_all | exact GlobalTheory.JumpStatement.holds_all | (intros; apply GlobalTheory.JumpStatement.holds_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_local_relation_dualNumber_cocycle : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  first | exact @GlobalTheory.TameRel.tame_relation | exact GlobalTheory.TameRel.tame_relation | (intros; apply GlobalTheory.TameRel.tame_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

noncomputable section

namespace GlobalTheory.HWL.IoLayer

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem sepRA' (LL : FinExt l) (e : OCb l) (he : ¬ IsUnit (e - 1)) (t : RA LL)
    (ht : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e = t) (x : RA LL)
    (hx : ∀ k, (t - 1) ^ k ∣ x) : x = 0 := by
  refine sepRA LL e he x ?_
  have h := tmul_sub_one LL (WittVector.teichmuller l e)
  rw [h, ht]
  exact hx

theorem teich_pow (LL : FinExt l) (e : OCb l) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (e ^ l) : RA LL) =
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e) ^ l := by
  have h1 : WittVector.teichmuller l (e ^ l) = (WittVector.teichmuller l e : Ainf l) ^ l := map_pow _ _ _
  rw [h1, Algebra.TensorProduct.tmul_pow, one_pow]

theorem γ₀_X_eq {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL} (R : WSer Γ)
    (g : ↥(GK K)) (c : ℤ_[l]) (hc : (c : ℚ_[l]) = (P.χQ g : ℚ_[l])) :
    R.γ₀ (Γ.resΓ g) X = PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) (binomialSeries ℤ_[l] c) - 1 := by
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  obtain ⟨_, _, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hlin : (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) c := by
    apply Subtype.ext
    have := Γ.χΓ_res g
    rw [P.PD_χ, ← hc] at this
    exact this
  have hact := (GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (R.γ₀ (Γ.resΓ g)) R.φ₀ c h0
    (R.γ₀_comm _) (R.γ₀_X _).1 ((R.γ₀_X _).2.trans hlin)).2
  rw [hact, (GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l ↥(OL LL)).1, GlobalTheory.Cyc.cyc]

set_option maxHeartbeats 1000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∃ I : IoS AI R, IoW I := by
  intro l _ P AI K s LL hG Γ R
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨u, hu, huniq⟩ := GlobalTheory.UnramIdem.exists_prod_hom l P K s LL hG Γ.emb Γ.emb_bij
  have he := εroot_sub_not_unit AI s
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 _ he
  obtain ⟨io, hπ, hc⟩ := let_exists
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1) : RA LL) u
  have hπ' := hπ.trans (tmul_sub_one LL _)
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  have h1 : io.comp (letφ R.φ₀) = (φRA LL).comp io := by
    have ht := teich_pow LL (AI.εroot s)
    have he' : ¬ IsUnit (AI.εroot s ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    refine comm_φ l R.φ₀ h0 io u hc (φRA LL) _ hπ' ((φRA_teich LL _).trans ht) ?_
      (sepRA' LL _ he' _ ht)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := hu (c ^ l) m hm hl
      (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hcm, one_pow]) (xb ^ l)
      (tilt_pow hxb l) (shift _ _ o) (fun i => by
        have := DFunLike.congr_fun (Γ.emb_σ (i - 1)) c
        rw [sub_add_cancel, AlgHom.comp_apply, sigma_root K c m hm hl hcm] at this
        rw [this]
        exact ho (i - 1))
    exact e2.trans ((congrArg (φRA LL) e1).trans (φRA_teich LL xb)).symm
  have h2 : ∀ g : ↥(GK K), io.comp (letγ (R.γ₀ (Γ.resΓ g))) = (gRA AI LL (g : GQ l)).comp io := by
    intro g
    obtain ⟨χ, hχ, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
    obtain ⟨⟨io0, hio0, -⟩, -⟩ := GlobalTheory.Cyc.IoMap.main l _ he
    have he' : ¬ IsUnit (AI.actT g (AI.εroot s) - 1) := fun h => he (by
      have := h.map (AI.actT g).symm
      rwa [map_sub, map_one, RingEquiv.symm_apply_apply] at this)
    have e0 := (io_zl LL _ _ he io hπ io0 hio0 (binomialSeries ℤ_[l] (χ g : ℤ_[l]))).trans
      (congrArg (fun w : Ainf l => ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL))
        (io_binomial AI s g _ (hχ g) io0 hio0))
    refine comm_γ _ _ (γ₀_X_eq R g _ (hχ g)) io u hc (gRA AI LL g) _ _ hπ' e0 (gRA_teich AI LL g _) ?_
      (sepRA' LL _ he' _ rfl)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := actT_tilt AI g c (g.2 ⟨c, c.2.1⟩) m hm hl xb hxb
    have e3 := gRA_teich AI LL g xb
    rw [e2] at e3
    exact e1.trans ((congrArg (gRA AI LL g) e1).trans e3).symm
  obtain ⟨I, hI⟩ := assemble R (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) _
    (φRA LL) (fun g : ↥(GK K) => gRA AI LL (g : GQ l)) (inclR_φRA LL) (fun g => inclR_gRA AI LL g)
    (by rw [P.PD_p]; exact (GlobalTheory.HWL.TensorWitt.main l LL).1) io hπ
    (isUnit_inclR LL _ (εroot_ne_one AI s)) h1 h2
  refine ⟨I, fun c m hm hl hcm xb hxb o ho => ?_⟩
  rw [hI, ← cst_apply, hc]
  exact hu c m hm hl hcm xb hxb o ho

end GlobalTheory.HWL.IoLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootPowIdealsTendstoZeroWeakTopStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerRootPow_ideals_tendsto_zero_weakTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U := by
  first | exact @GlobalTheory.WeakClosed.SmallW.main | exact GlobalTheory.WeakClosed.SmallW.main | (intros; apply GlobalTheory.WeakClosed.SmallW.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjectiveStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  first | exact @GlobalTheory.PSer.TshOnto.tsh_surjective | exact GlobalTheory.PSer.TshOnto.tsh_surjective | (intros; apply GlobalTheory.PSer.TshOnto.tsh_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem stepSub_holds : StepSub := by
  intro D i r ρ hr π hd Xs hπ
  obtain ⟨e, he⟩ := hd
  exact subTw_blocks D i r ρ hr π e he Xs hπ

end GlobalTheory.Pass
end

