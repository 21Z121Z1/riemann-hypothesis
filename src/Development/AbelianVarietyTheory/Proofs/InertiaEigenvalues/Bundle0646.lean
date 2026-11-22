import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPointsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admFon_of_points : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  first | exact @GlobalTheory.HubFon.main | exact GlobalTheory.HubFon.main | (intros; apply GlobalTheory.HubFon.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecompositionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_of_decomposition : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  first | exact @GlobalTheory.GTwoTheta.main | exact GlobalTheory.GTwoTheta.main | (intros; apply GlobalTheory.GTwoTheta.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Polynomial Cardinal

namespace GlobalTheory.LocGL

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_not_isUnit_sub [Nontrivial V] (hV : Module.rank ℂ V ≤ ℵ₀) (T : Module.End ℂ V) :
    ∃ c : ℂ, ¬ IsUnit (T - algebraMap ℂ _ c) := by
  first
  | exact @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | (apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub ..)

variable {G : Type} [Group G]

theorem exists_eq_smul_of_rank_le {π : Representation ℂ G V} (hi : π.IsIrreducible) (hV : Module.rank ℂ V ≤ ℵ₀)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨c, hc⟩ := exists_not_isUnit_sub hV T.toLinearMap
  let S : π.IntertwiningMap π := T - c • .id π
  rcases Representation.IsIrreducible.bijective_or_eq_zero S with h | h
  · exact absurd ((Module.End.isUnit_iff _).2 h) hc
  · exact ⟨c, fun v => sub_eq_zero.1 (congrArg (fun f : π.IntertwiningMap π => f v) h)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

theorem countable_orbit {π : Representation ℂ G V} (hs : IsSmooth π) (v : V) : (Set.range fun g => π g v).Countable := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense G
  refine (hD.image fun g => π g v).mono ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ ((hs v).preimage (continuous_const_mul g⁻¹)) ⟨g, by simp⟩
  refine ⟨x, hxD, ?_⟩
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem rank_le_aleph0_of_isIrreducible {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ V ≤ ℵ₀ := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ht : Submodule.span ℂ (Set.range fun g => π g v) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨f, rfl⟩ := orbitMap_surjective hi hv w
    show π.asAlgebraHom f v ∈ _
    induction f using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span ⟨g, by simp⟩
    | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem (ha trivial) (hb trivial)
    | smul c a ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (ha trivial)
  rw [← rank_top, ← ht]
  exact (rank_span_le _).trans (le_aleph0_iff_set_countable.2 (countable_orbit hs v))

theorem exists_eq_smul_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  exists_eq_smul_of_rank_le hi (rank_le_aleph0_of_isIrreducible hs hi) T

theorem algebraMap_intertwiningMap_bijective_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨fun a b h => smul_left_injective ℂ hv (congrArg (fun f : π.IntertwiningMap π => f v) h), fun T => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSmooth hs hi T
  exact ⟨c, by ext w; exact (hc w).symm⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k n) in

theorem secondCountableTopology_GL : SecondCountableTopology (GL n k) := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  have : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  have : SecondCountableTopology (Matrix n n k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem schur_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  haveI := secondCountableTopology_GL k n
  exists_eq_smul_of_isSmooth hs hi T

theorem algebraMap_intertwiningMap_bijective_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) :=
  haveI := secondCountableTopology_GL k n
  algebraMap_intertwiningMap_bijective_of_isSmooth hs hi

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem continuous_glScalar : Continuous (GeneralLinearGroup.scalar n : kˣ → GL n k) := by
  refine Units.continuous_map (f := (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom) ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isSmoothChar_of_hasCentralChar [Nontrivial V] {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : IsSmoothChar ω := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (ω.ker : Set kˣ) = GeneralLinearGroup.scalar n ⁻¹' {g | π g v = v} := by
    ext z
    show ω z = 1 ↔ π (GeneralLinearGroup.scalar n z) v = v
    rw [h]
    exact ⟨fun e => by simp [e], fun e => Units.ext (smul_left_injective ℂ hv (e.trans (one_smul _ _).symm))⟩
  show IsOpen (ω.ker : Set kˣ)
  rw [this]
  exact (hs v).preimage continuous_glScalar

theorem exists_smooth_hasCentralChar {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  have key : ∀ z : kˣ, ∃ c : ℂ, ∀ w, π (GeneralLinearGroup.scalar n z) w = c • w := fun z =>
    schur_GL hs hi ⟨π (GeneralLinearGroup.scalar n z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]⟩
  choose c hc using key
  have : ∃ ω, HasCentralChar π ω := by
    refine ⟨MonoidHom.toHomUnits ⟨⟨c, smul_left_injective ℂ hw₀ ?_⟩, fun x y => smul_left_injective ℂ hw₀ ?_⟩, hc⟩
    · simp [← hc]
    · simp only [← hc, mul_smul, map_mul, Module.End.mul_apply]
  obtain ⟨ω, hω⟩ := this
  exact ⟨ω, isSmoothChar_of_hasCentralChar hs hω, hω⟩

section CentralChar

variable {R : Type} [CommRing R]

theorem centralChar_unique [Nontrivial V] {π : Representation ℂ (GL n R) V} {ω ω' : Rˣ →* ℂˣ}
    (h : HasCentralChar π ω) (h' : HasCentralChar π ω') : ω = ω' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv ((h z v).symm.trans (h' z v)))

theorem hasCentralChar_of_equiv {π : Representation ℂ (GL n R) V} {σ : Representation ℂ (GL n R) W} (φ : π.Equiv σ)
    {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := fun z w => by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ _ (φ.toIntertwiningMap v) = _ • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem hasCentralChar_twist {π : Representation ℂ (GL n R) V} {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω)
    (χ : Rˣ →* ℂˣ) : HasCentralChar (twist π (detChar n χ)) (ω * χ ^ Fintype.card n) := fun z v => by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  rw [twist_apply, h, detChar_apply, this, smul_smul, mul_comm]
  simp

end CentralChar

namespace IrrGL

theorem pow_eq_of_tw_eq {x : IrrGL k} {χ ψ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} {hψ : IsSmoothChar ψ}
    (h : x.tw χ hχ = x.tw ψ hψ) : χ ^ x.1 = ψ ^ x.1 := by
  have := Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h)
  have h1 := centralChar_unique (V := x.2.rep.V) (hasCentralChar_of_equiv φ (hasCentralChar_twist hω χ)) (hasCentralChar_twist hω ψ)
  simpa using h1

theorem nu_ofReal_inj {x : IrrGL k} (hx : 0 < x.1) {s t : ℝ} : x.nu s = x.nu t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := pow_eq_of_tw_eq h
  have h2 : ∀ (s : ℂ) (m : ℕ), absPow k s ^ m = absPow k (m * s) := fun s m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← absPow_add]; congr 1; push_cast; ring
  rw [h2, h2] at h1
  have h3 : absPow k ((x.1 * (s - t) : ℝ) : ℂ) = 1 := by
    rw [show ((x.1 * (s - t) : ℝ) : ℂ) = x.1 * s + -(x.1 * t) by push_cast; ring, absPow_add, absPow_neg, h1,
      mul_inv_cancel]
  exact sub_eq_zero.1 ((mul_eq_zero.1 (absPow_ofReal_eq_one.1 h3)).resolve_left (Nat.cast_ne_zero.2 hx.ne'))

theorem nu_intCast_inj {x : IrrGL k} (hx : 0 < x.1) {a b : ℤ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

theorem nu_natCast_inj {x : IrrGL k} (hx : 0 < x.1) {a b : ℕ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

theorem nu_ofReal_eq_self {x : IrrGL k} (hx : 0 < x.1) {s : ℝ} : x.nu s = x ↔ s = 0 := by
  simpa using nu_ofReal_inj hx (s := s) (t := 0)

end IrrGL

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun _ _ h =>
  Fin.ext ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 h)

theorem nodup_ms (Δ : Segment k) : Δ.ms.Nodup := Finset.univ.nodup.map Δ.term_injective

theorem carrier_injective : Function.Injective (carrier : Segment k → Set (IrrGL k)) := fun Δ Δ' h => by
  have key : ∀ D : Segment k, D.first ∈ D.carrier := fun D => mem_carrier.2 ⟨0, D.len_pos, by simp⟩
  obtain ⟨a, -, ha⟩ := mem_carrier.1 (h ▸ key Δ)
  obtain ⟨b, -, hb⟩ := mem_carrier.1 (h.symm ▸ key Δ')
  have h0 : b + a = 0 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by
    rw [Nat.cast_add, ← IrrGL.nu_nu, hb, ha, Nat.cast_zero, IrrGL.nu_zero])
  obtain rfl : b = 0 := by omega
  refine ext_first (by simpa using hb) ?_
  rw [← card_ms, ← card_ms, (Multiset.Nodup.ext Δ.nodup_ms Δ'.nodup_ms).2 fun x => by rw [mem_ms, mem_ms, h]]

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem schur_and_segments (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
      IsSmooth π → π.IsIrreducible → Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) ∧
        ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω) ∧
    (∀ x : IrrGL k, 0 < x.1 → ∀ s t : ℝ, x.nu s = x.nu t ↔ s = t) ∧
    (∀ Δ : Segment k, Function.Injective Δ.term ∧ Δ.ms.Nodup) ∧
    Function.Injective (Segment.carrier : Segment k → Set (IrrGL k)) :=
  ⟨fun _ _ _ _ _ _ _ hs hi => ⟨algebraMap_intertwiningMap_bijective_GL hs hi, exists_smooth_hasCentralChar hs hi⟩,
    fun _ hx _ _ => IrrGL.nu_ofReal_inj hx, fun Δ => ⟨Δ.term_injective, Δ.nodup_ms⟩, Segment.carrier_injective⟩

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisDvdTauPowLPowAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.BSP.HeightSprime

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ d ρ hρ s Y hY hP
  obtain ⟨ι, TB, k, v, Z, hnull, hWZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hcol : ∀ i (b : Fin d), ∃ c : Fin d → bk.S, (fun a => v i a b) = Y *ᵥ fun a => bk.ev (c a) := by
    intro i b
    refine (hP _).1 ⟨fun a => Z i a b, fun j hj => ?_⟩
    funext a
    have h := congrFun (congrFun (hWZ j hj i) a) b
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  choose σc hσc using hcol
  set σ : ι → Matrix (Fin d) (Fin d) bk.S := fun i => Matrix.of fun a b => σc i b a with hσdef
  have hv : ∀ i, v i = Y * (σ i).map bk.ev := by
    intro i
    refine Matrix.ext fun a b => ?_
    have h := congrFun (hσc i b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, σ] using h
  have hσn := GlobalTheory.T.null_powerSeries_of_null_ainf_mul l K bk ι TB d Y hY σ (fun n a b => by simpa only [← hv] using hnull n a b)
  have hL : ∀ c b : Fin d, ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
    fun c b => GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family l K bk ι TB (fun i => σ i c b) (fun n => hσn n c b)
  choose L hL using hL
  refine ⟨k, Matrix.of L, ?_⟩
  refine Matrix.ext fun a b => ?_
  refine GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum l K bk ι TB (fun i => v i a b * TB.b i) _ _ ?_ ?_
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hsum a b
  · classical
    intro n
    choose F hF using fun c => hL c b n
    refine ⟨Finset.univ.biUnion F, fun G hG => ?_⟩
    have e : (Y * Matrix.of L) a b - ∑ i ∈ G, v i a b * TB.b i =
        ∑ c, Y a c * (L c b - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i) := by
      simp only [hv, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _
      (hF c G ((Finset.subset_biUnion_of_mem F (Finset.mem_univ c)).trans hG))
end GlobalTheory.BSP.HeightSprime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoTied

theorem blochKatoDim_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim (P.PD K) ↥LL.1 := by
  intro l _ P AI hT K LL _
  refine GlobalTheory.blochKatoDim_of_bkADim_of_fontCore l P K LL ?_
    (GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K)
    (GlobalTheory.LocalIntegers.good_integers l LL).1
  intro LL' _ _ _ O _ _ hO A hdr
  exact (GlobalTheory.SeqDim.h1f_finrank l P AI hT K LL' O hO A hdr).2

end GlobalTheory.BlochKatoTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrismStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.StratCocycle.unit_cocycle | exact GlobalTheory.BSP.StratCocycle.unit_cocycle | (intros; apply GlobalTheory.BSP.StratCocycle.unit_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  first | exact @GlobalTheory.envelope_dvd_lpow_of_sections | exact GlobalTheory.envelope_dvd_lpow_of_sections | (intros; apply GlobalTheory.envelope_dvd_lpow_of_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), lem3 D HW F := by
  first | exact @GlobalTheory.NL.CokerKill.X_pow_kills_coker | exact GlobalTheory.NL.CokerKill.X_pow_kills_coker | (intros; apply GlobalTheory.NL.CokerKill.X_pow_kills_coker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLagTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open Filter
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.TermCont

open GlobalTheory.RawLift

theorem continuous_lagTerm : ∀ D : D7, ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
        Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ Y _
  have hw := hS.weil
  have hψ := hw.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ h₂
  have hJ := GlobalTheory.ThetaJointCont.continuous_om_oriented hw h₁
  have hrm : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E), Continuous fun u : WO V W => ratMul C u := fun C => by
    unfold ratMul
    exact continuous_const.matrix_mul continuous_id
  have hμ1 : μ 𝓕 = 1 := hS.covol.2.2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ1]; exact ENNReal.one_ne_top)
  have : SecondCountableTopology (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).2.1
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  have hc0 : Continuous fun w : WO V W => om ((1 : GA D V), g₀) f₁ w :=
    hJ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  have hev : ∀ᶠ g in 𝓝 g₀, ∀ w ∈ K, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun w hw' => ?_
    have hc : Continuous fun y : GA D W × WO V W => ‖om ((1 : GA D V), y.1) f₁ y.2‖ :=
      (hJ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).norm
    exact (hc.continuousAt.eventually_lt continuousAt_const ((hκ w hw').trans_lt (lt_add_one κ))).mono
      fun y hy => hy.le
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ w, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := hev.mono fun g hg w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hw.om_pres _ f₁ h₁) γ hγ w]
    exact hg _ h
  unfold lagTerm
  refine continuousAt_of_dominated (bound := fun _ => (κ + 1) * C₂) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((((hw.om_pres _ f₁ h₁).cont.comp (hrm _)).mul
      (continuous_star.comp (h₂.cont.comp (hrm _))))).aestronglyMeasurable
  · refine hall.mono fun g hg => Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hg _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hg 0))
  · refine Eventually.of_forall fun u => ?_
    exact ((hw.om_cont f₁ h₁ _).comp (continuous_const.prodMk continuous_id)).continuousAt.mul continuousAt_const

end GlobalTheory.RawLift.TermCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransformStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_colT_good | exact GlobalTheory.CuspGeneric.continuous_colT_good | (intros; apply GlobalTheory.CuspGeneric.continuous_colT_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariantsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.CrisCoord.lattice_basis_span_invariants | exact GlobalTheory.CrisCoord.lattice_basis_span_invariants | (intros; apply GlobalTheory.CrisCoord.lattice_basis_span_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficientsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_local_coefficients : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → SumRepresentations.At.G2 D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → GlobalTheory.PtCore.ChiOneE D i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  first | exact @GlobalTheory.DualTwistCrys.main | exact GlobalTheory.DualTwistCrys.main | (intros; apply GlobalTheory.DualTwistCrys.main <;> assumption)
end

