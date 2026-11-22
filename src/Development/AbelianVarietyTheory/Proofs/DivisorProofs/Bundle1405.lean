import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.CuspMult GlobalTheory.PRep
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDec

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mem_fixed {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X} {K : Subgroup H} {x : X} :
    x ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixed, eig]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ρ : Representation ℂ H V}

theorem isSemisimple (ha : IsAdmissible ρ) (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {K₀ : Subgroup H}
    (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : ρ.IsSemisimpleRepresentation :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc

theorem mem_irrSum {W X : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ H W}
    {ρ : Representation ℂ H X} {C : Submodule ℂ X} (h1 : σ.IsSemisimpleRepresentation) (h2 : IsAdmissible σ)
    {f : W →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1
  have hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ H) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hs
  refine Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    obtain ⟨U, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m
    have hU : U.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm
      exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)
    exact GlobalTheory.RepCount.apply_mem_irrSum hU
      (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2)
      (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩
  · simp
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

theorem isDecomp_of_form {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (hC : ∀ g, ∀ x ∈ C, ρ g x ∈ C) (B : X → X → ℂ)
    (hl : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z ∧ B y x = star (B x y))
    (hp : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) (hi : ∀ g, ∀ x ∈ C, ∀ y ∈ C, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ fixed ρ K))
    {K₀ : Subgroup H} (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : IsDecomp ρ C := by
  intro x hx hx'
  let A : Subrepresentation ρ := ⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩
  have hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y) := fun x hx y hy => (hl x hx y hy y hy 0).2
  have h0 : ∀ x ∈ C, B x 0 = 0 := fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1
  let cd : InnerProductSpace.Core ℂ A.toSubmodule :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm
      re_inner_nonneg := fun a => by
        by_cases h : (a : X) = 0
        · simp [h, h0 0 C.zero_mem]
        · exact (hp _ a.2.1 h).le
      add_left := fun a b c => by
        have := (hl _ c.2.1 _ a.2.1 _ b.2.1 1).1
        rw [one_smul, one_mul] at this
        show B (a + b) c = B a c + B b c
        rw [hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]
      smul_left := fun a b r => by
        have := (hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1
        rw [zero_add, h0 _ b.2.1, zero_add] at this
        show B (r • a) b = star r * B a b
        rw [hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]
      definite := fun a h => by
        by_contra hn
        have := hp _ a.2.1 fun e => hn (Subtype.ext e)
        rw [show B a a = 0 from h] at this
        simp at this }
  have ha : IsAdmissible A.toRepresentation := by
    refine ⟨fun v => ?_, fun K hK _ => ?_⟩
    · have : {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v} := by
        ext g
        exact Subtype.ext_iff
      rw [this]
      exact v.2.2
    · haveI := hf K hK
      refine FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K)
        (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_
      have h' : (a.1 : X) = b.1 := congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
  have hs : A.toRepresentation.IsSemisimpleRepresentation := by
    letI := cd.toNormedAddCommGroup
    letI := InnerProductSpace.ofCore cd.toCore
    exact isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc
  exact mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩

end Abstract

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : DSModel V S}

theorem finRep_mem (g : GfC V) (T : MMap M) (hT : T ∈ allMaps θ M) : finRep M g T ∈ allMaps θ M := by
  have e : finRep M g T = heckeOn M {(g : GA D V)} T := by
    ext v x
    simp [heckeOn, postOn_apply, heckeLin_apply, finRep_apply]
  rw [e]
  exact Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)

theorem isMultiplicityInner_finRep {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (g : GfC V) {T T' : MMap M} (hT : T ∈ allMaps θ M) (hT' : T' ∈ allMaps θ M)
    {c : ℂ} (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 (finRep M g T) (finRep M g T') c := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  intro v v'
  have := GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by
    rw [(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]
  exact ⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩

theorem finiteDimensional_fixed (hP : GlobalTheory.Published.HarishChandraFinite) (hθ : IsInfFam θ) (K : Subgroup (GfC V))
    (hK : IsOpen (K : Set (GfC V))) : FiniteDimensional ℂ ↥(allMaps θ M ⊓ fixed (finRep M) K) := by
  obtain ⟨N, hN, e⟩ := isOpen_induced_iff.1 hK
  have hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K := fun k => Set.ext_iff.1 e k
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))
  haveI := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ
    ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_
  have h := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩
  have := congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))
  rw [one_mul]
  exact this

theorem exists_compact_open (V : HSp D) : ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) := by
  obtain ⟨_, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨N, hN, h1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1
  refine ⟨U.subgroupOf (GfC V), hU.preimage continuous_subtype_val, ?_⟩
  refine ((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset
    ((U.isClosed_of_isOpen hU).preimage continuous_subtype_val) fun k hk => hUN k hk k.2

theorem cuspDecomp : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, CuspDecomp D := by
  intro hP hQ D θ hθ V S M
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, hF⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2
  have hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕 := GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨K, ho, hc⟩ := exists_compact_open V
  refine isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_)
    (finiteDimensional_fixed hP hθ) ho hc
  have h := isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))
  exact hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h

end GlobalTheory.CuspDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFuStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU E n, {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.SuppFin.suppFin | exact GlobalTheory.BCT.SuppFin.suppFin | (intros; apply GlobalTheory.BCT.SuppFin.suppFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TotPosSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embReal_algebraMap {w : InfinitePlace F} (hw : w.IsReal) (t : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion t) =
      InfinitePlace.embedding_of_isReal hw t := by
  have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm t)
  simpa using this

theorem eta_inf_eq_one [Algebra.IsQuadraticExtension F E] {w : InfinitePlace F} (hw : w.IsReal) (t : Fˣ)
    (ht : 0 < InfinitePlace.embedding_of_isReal hw (t : F)) :
    GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
  rw [GlobalTheory.QuadSymbol.eta_eq_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff]
  set g := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set a : w.Completion := algebraMap F w.Completion (t : F)
  have hga : g a = InfinitePlace.embedding_of_isReal hw (t : F) := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, embReal_algebraMap]
  refine ⟨algebraMap w.Completion (w.Completion ⊗[F] E) (g.symm (Real.sqrt (g a))), ?_⟩
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E,
    ← map_pow, Real.sq_sqrt (hga ▸ ht.le), RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  change (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v x) =
    (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v y)
  rw [h]

theorem valued_eq_exp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem eta_inert [Algebra.IsQuadraticExtension F E] {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F) x = (-1) ^ ordL (x : v.adicCompletion F) := by
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let χ : (v.adicCompletion F)ˣ →* ℤˣ :=
    MonoidHom.mk' (GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F)) ((GlobalTheory.QuadSymbol.localCharacters F E).1 v)
  set π := atFin v (unif v)
  set k := ordL (x : v.adicCompletion F)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec v
  set u := x * π ^ (-k)
  have hu1 : IsUnitAt v u := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, valued_eq_exp x.ne_zero,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [k]
  have hx : x = u * π ^ k := by simp [u]
  have e1 : χ u = 1 := GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hu1)
  have e2 : χ π = -1 := GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
    (GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hv hu (unif_spec v))
  change χ x = _
  rw [hx, map_mul, map_zpow, e1, e2, one_mul]

end Loc

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSplit_under {w : Pl E} (h : IsSplitAt w) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  obtain ⟨u, hne, hu⟩ := h
  exact GlobalTheory.LFun.isSplit_iff.2 ⟨u, w, hne, hu, rfl⟩

theorem not_isSplit_under {w : Pl E} (h : ¬ IsSplitAt w) : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  rintro hs
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  by_cases haw : a = w
  · subst haw
    exact h ⟨b, hab.symm, hb⟩
  · exact h ⟨a, haw, ha⟩

theorem isUnram_of_unr (hU : Unr E) (v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
  GlobalTheory.LFun.isUnram_iff.2 fun P _ => by
    haveI := hU P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem neg_one_zpow_cast (k : ℤ) : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp

theorem term_eq (hU : Unr E) (w : Pl E) (t : Units ↥(maximalRealSubfield E)) :
    (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) (algebraMap ↥(maximalRealSubfield E) E t))) =
      ((GlobalTheory.QuadSymbol.eta ↥(maximalRealSubfield E) E ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))
        (GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E)))) : ℤ) : ℂ) := by
  have h2 : Module.finrank ↥(maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ↥(maximalRealSubfield E) E
  split_ifs with hs
  · rw [GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isSplit h2 (isSplit_under hs) _)]
    simp
  · rw [eta_inert (not_isSplit_under hs) (isUnram_of_unr hU _), neg_one_zpow_cast]
    congr 1
    refine ordL_congr ?_
    have hx : ((GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E))) : (w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))) =
        algebraMap ↥(maximalRealSubfield E) _ (t : ↥(maximalRealSubfield E)) := rfl
    have e := GlobalTheory.LFun.valued_complMap (F := ↥(maximalRealSubfield E)) (E := E) (w := w) rfl
      (a := algebraMap ↥(maximalRealSubfield E) ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E)) (t : ↥(maximalRealSubfield E))) (by simp)
    rw [GlobalTheory.LFun.isUnram_iff.1 (isUnram_of_unr hU _) w rfl, pow_one, GlobalTheory.LFun.complMap_algebraMap] at e
    rw [hx, e]

theorem bijOn_under {S : Set (Pl E)} (hS : IsSection S) :
    Set.BijOn (fun w : Pl E => w.under (𝓞 ↥(maximalRealSubfield E))) S Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun v _ => ?_⟩
  · obtain ⟨u, -, hu⟩ := hS a
    exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, hab.symm⟩).symm
  · obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over ↥(maximalRealSubfield E) E).2.1 v
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
    exact ⟨u, hu, hu'.trans hw⟩

end CM

end GlobalTheory.TotPosSign

namespace GlobalTheory.UnitaryClasses

open GlobalTheory.TotPosSign in

theorem signProd_totPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S →
    ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) →
    ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  intro E _ _ _ hU S hS d hd hpos
  have hmem : d ∈ maximalRealSubfield E := (mem_maximalRealSubfield_iff d).2 fun φ => by
    obtain ⟨r, -, hr⟩ := hpos φ
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  set t0 : ↥(maximalRealSubfield E) := ⟨d, hmem⟩
  have ht0 : algebraMap (↥(maximalRealSubfield E)) E t0 = d := rfl
  have ht0' : t0 ≠ 0 := fun h => hd (by rw [← ht0, h, map_zero])
  set t := Units.mk0 t0 ht0'
  have PF := GlobalTheory.QuadSymbol.productFormula (↥(maximalRealSubfield E)) E t
  have hinf : ∀ w : InfinitePlace ↥(maximalRealSubfield E),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E w.Completion (GlobalTheory.QuadSymbol.infDiag _ t w) = 1 := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    refine eta_inf_eq_one hw t ?_
    letI : Algebra (↥(maximalRealSubfield E)) ℂ := w.embedding.toAlgebra
    let τ : E →ₐ[↥(maximalRealSubfield E)] ℂ := IsAlgClosed.lift
    obtain ⟨r, hr, e⟩ := hpos τ.toRingHom
    have e2 : (InfinitePlace.embedding_of_isReal hw (t : ↥(maximalRealSubfield E)) : ℂ) = r := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← e]
      exact (τ.commutes t0).symm
    rw [Complex.ofReal_inj] at e2
    rw [e2]; exact hr
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v) = 1 := by
    have h := PF.2
    unfold GlobalTheory.QuadSymbol.etaProd at h
    rwa [Finset.prod_eq_one fun w _ => hinf w, mul_one] at h
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hd' : d = algebraMap (↥(maximalRealSubfield E)) E ((t : Units ↥(maximalRealSubfield E)) : ↥(maximalRealSubfield E)) := rfl
  rw [hd', finprod_mem_eq_of_bijOn _ (bijOn_under hS) (g := fun v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)) => cz
      (GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v))) fun w _ => term_eq hU w t,
    finprod_mem_univ, ← MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport PF.1), hfin, map_one]

end GlobalTheory.UnitaryClasses

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2DiagonalOne
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl
  rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem coefM_one (z : ℂ) : coefM z 1 = z := by
  simp [coefM, Complex.ext_iff]

theorem coefM_neg_one (z : ℂ) : coefM z (-1) = star z := by
  simp [coefM, Complex.ext_iff]

theorem coefD_one (z : ℂ) : coefD z 1 = -star z := by
  simp [coefD, Complex.ext_iff]

theorem coefD_neg_one (z : ℂ) : coefD z (-1) = -z := by
  simp [coefD, Complex.ext_iff]

theorem heisOp_eq_sum_mul_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  intro P Q R S c
  unfold heisOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ -
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [raiB, lowB, linePos, lineSign, coefM_one, coefM_neg_one, coefD_one, coefD_neg_one, if_true,
      Bool.false_eq_true, if_false] <;>
    module

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsRealISmulSignConjO
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.HeisRot

theorem jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem jm_conj_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq, jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) (l : Ln P Q R S) :
    ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2 • raiB l
      - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 *
          star ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)
      = ((t : ℂ) * Complex.I) • ((c l.1 l.2 • raiB l
          - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)) := by
  obtain ⟨a, b⟩ := l
  rw [Matrix.smul_apply, jm_conj_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [raiB, lowB, linePos, lineSign, Complex.conj_ofReal, smul_smul] <;> ring_nf

theorem heisOp_rot_one (P Q R S : ℕ) (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 := by
  unfold heisOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun l _ => term_eq c t l), ← Finset.smul_sum, smul_comm]

end GlobalTheory.HeisRot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := by
  first | exact @GlobalTheory.RealLift.PolRangePf.polRange_of | exact GlobalTheory.RealLift.PolRangePf.polRange_of | (intros; apply GlobalTheory.RealLift.PolRangePf.polRange_of <;> assumption)
end

