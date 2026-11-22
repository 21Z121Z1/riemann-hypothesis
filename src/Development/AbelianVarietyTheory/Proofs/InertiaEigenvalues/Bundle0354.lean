import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecGalois

theorem exists_continuousMulEquiv : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  intro p _ F Ω _ _ _ _ _ A j hj
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  let e2 : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K.1] PadicAlgCl p) :=
    e.trans (IntermediateField.fixingSubgroupEquiv K.1)
  refine ⟨{ e2 with continuous_toFun := hf.comp he, continuous_invFun := he'.comp hf' }, fun g x => ?_⟩
  exact hec g x

end GlobalTheory.DecGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Semilinear

theorem exists_equiv_map_lattice {O K U U' : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup U'] [Module K U'] [Module O U'] [IsScalarTower O K U']
    (A : Submodule O U) (B : Submodule O U') [A.IsLattice K] [B.IsLattice K]
    (h : Module.finrank K U = Module.finrank K U') :
    ∃ g : U ≃ₗ[K] U', A.map (g.toLinearMap.restrictScalars O) = B := by
  have key : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (C : Submodule O V)
      [C.IsLattice K], ∃ c : Module.Basis (Fin (Module.finrank K V)) K V, Submodule.span O (Set.range c) = C := by
    intro V _ _ _ _ C _
    let c₀ := Module.finBasis O C
    let c₁ := c₀.extendOfIsLattice K
    have hn : Module.finrank K V = Module.finrank O C := by
      rw [Module.finrank_eq_card_basis c₁, Fintype.card_fin]
    refine ⟨c₁.reindex (finCongr hn.symm), ?_⟩
    rw [Module.Basis.range_reindex]
    have h1 : Set.range c₁ = C.subtype '' Set.range c₀ := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact c₀.extendOfIsLattice_apply K i
    rw [h1, ← Submodule.map_span, c₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨a, ha⟩ := key A
  obtain ⟨b, hb⟩ := key B
  refine ⟨a.equiv b (finCongr h), ?_⟩
  rw [← ha, ← hb, Submodule.map_span, ← Set.range_comp, ← (finCongr h).surjective.range_comp b]
  congr 2
  funext i
  simp

theorem exists_semilinear {L V O K U : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V]
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U] (e : L →+* K)
    (S : Set V) (hS : S.Finite) (hspan : Submodule.span L S = ⊤) (B : Submodule O U) [B.IsLattice K]
    (h : Module.finrank L V = Module.finrank K U) :
    ∃ f : V →ₛₗ[e] U,
      (∀ (ι : Type) (b : Module.Basis ι L V), LinearIndependent K (fun i => f (b i)) ∧
        Submodule.span K (Set.range fun i => f (b i)) = ⊤) ∧ Submodule.span O (f '' S) = B := by
  classical
  let b₀ := Module.finBasis L V
  let f₀ : V →ₛₗ[e] (Fin (Module.finrank L V) → K) :=
    { toFun := fun x i => e (b₀.repr x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun c x => by funext i; simp }
  have hf₀ : ∀ T : Set V, Submodule.span L T = ⊤ → Submodule.span K (f₀ '' T) = ⊤ := by
    intro T hT
    have h1 : ∀ x, f₀ x ∈ Submodule.span K (f₀ '' T) := fun x => by
      have hx : x ∈ Submodule.span L T := hT ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    rw [eq_top_iff, ← (Pi.basisFun K (Fin (Module.finrank L V))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : Pi.basisFun K (Fin (Module.finrank L V)) i = f₀ (b₀ i) := by
      funext j
      show _ = e (b₀.repr (b₀ i) j)
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [h2]
    exact h1 _
  let A : Submodule O (Fin (Module.finrank L V) → K) := Submodule.span O (f₀ '' S)
  haveI : A.IsLattice K :=
    ⟨Submodule.fg_span (hS.image _), by rw [Submodule.span_span_of_tower, hf₀ S hspan]⟩
  obtain ⟨g, hg⟩ := exists_equiv_map_lattice (K := K) A B (by rw [← h]; simp)
  refine ⟨g.toLinearMap.comp f₀, fun ι b => ?_, ?_⟩
  · haveI : Finite ι := Module.Finite.finite_basis b
    haveI := Fintype.ofFinite ι
    have h1 : Submodule.span K (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = ⊤ := by
      have h2 : (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = g.toLinearMap '' (f₀ '' Set.range b) := by
        rw [← Set.range_comp, ← Set.range_comp]; rfl
      rw [h2, ← Submodule.map_span, hf₀ _ b.span_eq, Submodule.map_top]
      exact g.range
    exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank h1.ge
      (by rw [← h, Module.finrank_eq_card_basis b]), h1⟩
  · rw [← hg, Submodule.map_span, Set.image_image]
    rfl

theorem form_gen {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    Module.Finite L V ∧ {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨Module.Finite.of_basis b, T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

theorem baseChange_lattice {A B V : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) :
    Module.finrank (FractionRing B) (FractionRing B ⊗[A] V) = Module.finrank (FractionRing A) V ∧
      (Submodule.span B ((TensorProduct.mk A (FractionRing B) V 1) '' (Λ : Set V))).IsLattice (FractionRing B) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  refine ⟨?_, ?_, ?_⟩
  · rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A (FractionRing A) (FractionRing B) (FractionRing B) V).finrank_eq,
      Module.finrank_baseChange, (NChoice.fracEquiv A V).finrank_eq]
  · obtain ⟨T, rfl⟩ := hfg
    rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower]
    exact Submodule.fg_span (T.finite_toSet.image _)
  · rw [Submodule.span_span_of_tower, eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add y z hy hz => exact Submodule.add_mem _ hy hz
    | tmul a v =>
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) (FractionRing A) (Λ : Set V) v
        (hspan ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at hd
      have hd0 : algebraMap A (FractionRing B) d ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (FractionRing B))).2 (nonZeroDivisors.coe_ne_zero d)
      have h1 : a ⊗ₜ[A] v = (a * (algebraMap A (FractionRing B) d)⁻¹) • ((1 : FractionRing B) ⊗ₜ[A] ((d : A) • v)) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def (d : A), mul_one, smul_eq_mul,
          mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hd, rfl⟩)

end Semilinear

section Series

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : IntegralHeckeForms.ExpDat Y)

theorem twOK_one (i : X.Tw) (k : ℕ) : IntegralHeckeForms.TwOK i k ∅ (1 : G D.host.E N.Om →* (X.Ok i k)ˣ) := by
  refine ⟨by simp, by simp, by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun g g' _ => by simp, fun g => Subgroup.one_mem _, fun v A _ => by simp,
    fun v _ A _ σ _ => rfl⟩

theorem th_fg (h : IntegralHeckeForms.admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    (IntegralHeckeForms.Th Y i j b (IntegralHeckeForms.SgJ Y E i j b)).FG := by
  have h1 := h i hi j hj b 0 ∅ 1 (twOK_one i 0) _ subset_rfl
  haveI := X.Ok_fin i 0
  haveI : FaithfulSMul (X.O i) (X.Ok i 0) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i 0)
  haveI : Module.FaithfullyFlat (X.O i) (X.Ok i 0) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h2 : (((Y.MtLat i j b 0 ∅ 1).map (Y.thP i j b 0 ∅ 1)).restrictScalars (X.O i)).FG :=
    ((Y.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let m := TensorProduct.mk (X.O i) (X.Ok i 0) (Y.Fm i j b) 1
  refine Submodule.fg_of_fg_map_injective m (Module.FaithfullyFlat.tensorProduct_mk_injective _) (h2.of_le ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine h1 (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩))
  rw [Y.thPsi_one]
  rfl

theorem exists_basisOf (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (h : (IntegralHeckeForms.Th Y i j b Sg).FG) :
    ∃ S : Finset (Y.Dat i j b), IntegralHeckeForms.BasisOf Y i j b Sg S := by
  classical
  have hr : Submodule.span (X.O i) (Set.range fun a : Sg => IntegralHeckeForms.AO Y i j b (Y.th i j b a)) =
      (IntegralHeckeForms.Th Y i j b Sg).map (IntegralHeckeForms.AO Y i j b) := by
    rw [IntegralHeckeForms.Th, Submodule.map_span, Set.image_image, Set.image_eq_range]
  obtain ⟨S, h1, h2⟩ := exists_subbasis (X.O i) (Y.Fm i j b) Sg (fun a => IntegralHeckeForms.AO Y i j b (Y.th i j b a))
    (fun c w hc hw => by
      rw [← algebraMap_smul (FractionRing (X.O i)) c w, smul_eq_zero] at hw
      exact hw.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hc))
    (hr ▸ h.map _)
  refine ⟨S.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 ha
    exact a'.2
  · let e : S ≃ (S.map (Function.Embedding.subtype (· ∈ Sg)) : Finset _) :=
      Equiv.ofBijective (fun a => ⟨a.1.1, Finset.mem_map.2 ⟨a.1, a.2, rfl⟩⟩)
        ⟨fun a a' h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)), fun ⟨y, hy⟩ => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
          exact ⟨⟨a, ha⟩, rfl⟩⟩
    exact (linearIndependent_equiv e).1 h1
  · rw [← hr, ← h2, Finset.coe_map, Set.image_image]
    rfl

end Series

end GlobalTheory.TwistChoice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.LzExist

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsDecomp (S : Finset A) : Prop :=
  (∀ e ∈ S, e * e = e) ∧ (∀ e ∈ S, ∀ z : A, e * z = z * e) ∧ (∀ e ∈ S, e ≠ 0) ∧
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → e * f = 0) ∧ ∑ e ∈ S, e = 1

def IsPrim (S : Finset A) : Prop :=
  ∀ t ∈ S, ∀ x : A, x * x = x → (∀ z, x * z = z * x) → x * t = x → x = 0 ∨ x = t

theorem linInd {S : Finset A} (h : IsDecomp S) : LinearIndependent ℂ (fun x : S => (x : A)) := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : (∑ j ∈ s, c j • (j : A)) * (i : A) = c i • (i : A) := by
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, h.1 _ i.2]
    · intro j _ hji
      rw [smul_mul_assoc, h.2.2.2.1 _ j.2 _ i.2 (fun e => hji (Subtype.ext e)), smul_zero]
    · intro h'; exact absurd hi h'
  rw [hs, zero_mul] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right (h.2.2.1 _ i.2)

theorem card_le [Module.Finite ℂ A] {S : Finset A} (h : IsDecomp S) : S.card ≤ Module.finrank ℂ A := by
  have := (linInd h).fintype_card_le_finrank
  simpa using this

theorem refine_decomp [DecidableEq A] {S : Finset A} (h : IsDecomp S) {t : A} (ht : t ∈ S) {x : A}
    (hx : x * x = x) (hc : ∀ z, x * z = z * x) (hxt : x * t = x) (h0 : x ≠ 0) (ht' : x ≠ t) :
    IsDecomp (insert x (insert (t - x) (S.erase t))) ∧
      (insert x (insert (t - x) (S.erase t))).card = S.card + 1 := by
  obtain ⟨hI, hC, hN, hO, hS⟩ := h
  have htx : t * x = x := by rw [← hc t, hxt]
  have hxs : ∀ s ∈ S.erase t, x * s = 0 := by
    intro s hs
    obtain ⟨hst, hs⟩ := Finset.mem_erase.1 hs
    rw [← hxt, mul_assoc, hO t ht s hs (Ne.symm hst), mul_zero]
  have hsx : ∀ s ∈ S.erase t, s * x = 0 := fun s hs => by rw [← hc s]; exact hxs s hs
  have hts : ∀ s ∈ S.erase t, (t - x) * s = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [sub_mul, hO t ht s hs' (Ne.symm hst), hxs s hs, sub_zero]
  have hst' : ∀ s ∈ S.erase t, s * (t - x) = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [mul_sub, hO s hs' t ht hst, hsx s hs, sub_zero]
  have hxtx : x * (t - x) = 0 := by rw [mul_sub, hxt, hx, sub_self]
  have htxx : (t - x) * x = 0 := by rw [sub_mul, htx, hx, sub_self]
  have htt : (t - x) * (t - x) = t - x := by
    rw [mul_sub, htxx, sub_zero, sub_mul, hI t ht, hxt]
  have htx0 : t - x ≠ 0 := fun h => ht' (sub_eq_zero.1 h).symm
  have hnot : ∀ y, y * y = y → y ≠ 0 → (∀ s ∈ S.erase t, y * s = 0) → y ∉ S.erase t := by
    intro y hy hy0 hys hmem
    exact hy0 (by rw [← hy]; exact hys y hmem)
  have hm1 : t - x ∉ S.erase t := hnot _ htt htx0 hts
  have hm2 : x ∉ insert (t - x) (S.erase t) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun e => h0 ?_, hnot _ hx h0 hxs⟩
    rw [← hx]; nth_rewrite 2 [e]; exact hxtx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hx
    · exact htt
    · exact hI e (Finset.mem_of_mem_erase he)
  · intro e he z
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hc z
    · rw [sub_mul, mul_sub, hC t ht z, hc z]
    · exact hC e (Finset.mem_of_mem_erase he) z
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact h0
    · exact htx0
    · exact hN e (Finset.mem_of_mem_erase he)
  · intro e he f hf hef
    rw [Finset.mem_insert, Finset.mem_insert] at he hf
    rcases he with rfl | rfl | he <;> rcases hf with rfl | rfl | hf
    · exact absurd rfl hef
    · exact hxtx
    · exact hxs f hf
    · exact htxx
    · exact absurd rfl hef
    · exact hts f hf
    · exact hsx e he
    · exact hst' e he
    · exact hO e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · rw [Finset.sum_insert hm2, Finset.sum_insert hm1, ← add_assoc, add_sub_cancel,
      Finset.add_sum_erase S (fun e => e) ht, hS]
  · rw [Finset.card_insert_of_notMem hm2, Finset.card_insert_of_notMem hm1,
      Finset.card_erase_of_mem ht]
    have := Finset.card_pos.2 ⟨t, ht⟩
    omega

theorem exists_prim [Module.Finite ℂ A] [Nontrivial A] : ∃ S : Finset A, IsDecomp S ∧ IsPrim S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset A, IsDecomp S ∧ S.card = n
  have h1 : P 1 := ⟨{1}, ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp⟩
  have hb : ∀ n, P n → n ≤ Module.finrank ℂ A := by
    rintro n ⟨S, hS, rfl⟩; exact card_le hS
  obtain ⟨S, hS, hc⟩ := Nat.findGreatest_spec (P := P) (m := 1) (n := Module.finrank ℂ A) (hb 1 h1) h1
  refine ⟨S, hS, ?_⟩
  intro t ht x hx hc' hxt
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h2, h3⟩ := refine_decomp hS ht hx hc' hxt hne.1 hne.2
  have := Nat.le_findGreatest (P := P) (hb _ ⟨_, h2, rfl⟩) ⟨_, h2, rfl⟩
  omega

theorem lab_unique {ι : Type} {S : Finset A} (hS : IsDecomp S) (hP : IsPrim S) (e : ι → A)
    (he_idem : ∀ i, e i * e i = e i) (he_c : ∀ i z, e i * z = z * e i)
    (he_o : ∀ i j, i ≠ j → e i * e j = 0) (T : Finset ι) (hT : ∑ i ∈ T, e i = 1) {t : A} (ht : t ∈ S) :
    ∃ i ∈ T, e i * t = t ∧ ∀ j, j ≠ i → e j * t = 0 := by
  have key : ∀ j, e j * t = 0 ∨ e j * t = t := by
    intro j
    refine hP t ht _ ?_ ?_ ?_
    · rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e j), mul_assoc, hS.1 t ht, ← mul_assoc, he_idem]
    · intro z
      rw [mul_assoc, hS.2.1 t ht z, ← mul_assoc, he_c j z, mul_assoc]
    · rw [mul_assoc, hS.1 t ht]
  have hsum : ∑ j ∈ T, e j * t = t := by rw [← Finset.sum_mul, hT, one_mul]
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hS.2.2.1 t ht)
  have hit : e i * t = t := (key i).resolve_left hne
  refine ⟨i, hi, hit, fun j hji => (key j).resolve_right fun hjt => hS.2.2.1 t ht ?_⟩
  have h0 : (e j * t) * (e i * t) = 0 := by
    rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e i), mul_assoc, ← mul_assoc (e j), he_o j i hji,
      zero_mul]
  rw [hjt, hit, hS.1 t ht] at h0
  exact h0

end Alg

section Lz

variable (g r : ℕ) [Fact g.Prime] (e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))

abbrev GA (a : ℕ) : Type := MonoidAlgebra ℂ (GL (Fin a) (ZMod g))

def decS (a : ℕ) : Finset (GA g a) := (exists_prim (A := GA g a)).choose

theorem decS_spec (a : ℕ) : IsDecomp (decS g a) ∧ IsPrim (decS g a) :=
  (exists_prim (A := GA g a)).choose_spec

def LabQ (a : ℕ) (x : GA g a) (f : (ZMod g)[X]) : Prop :=
  (f.Monic ∧ f.natDegree = a ∧ f.coeff 0 ≠ 0) ∧
    ∀ h : a = r, e f * cast (congrArg (GA g) h) x = cast (congrArg (GA g) h) x

open Classical in

def labF (a : ℕ) (x : GA g a) : (ZMod g)[X] :=
  if h : ∃ f, LabQ g r e a x f then h.choose else (X - C 1) ^ a

theorem labF_spec (a : ℕ) (x : GA g a) :
    (labF g r e a x).Monic ∧ (labF g r e a x).natDegree = a ∧ (labF g r e a x).coeff 0 ≠ 0 := by
  unfold labF
  split_ifs with h
  · exact h.choose_spec.1
  · refine ⟨(monic_X_sub_C 1).pow a, ?_, ?_⟩
    · rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · rw [coeff_zero_eq_eval_zero]; simp

def lzE : PairedCharacterCondition.LzData g where
  Irr a := ↥(decS g a)
  finIrr a := inferInstance
  idem τ := τ.1
  idem_idem τ := (decS_spec g _).1.1 _ τ.2
  idem_central τ z := (decS_spec g _).1.2.1 _ τ.2 z
  idem_ne τ := (decS_spec g _).1.2.2.1 _ τ.2
  idem_orth τ σ h := (decS_spec g _).1.2.2.2.1 _ τ.2 _ σ.2 (fun e => h (Subtype.ext e))
  idem_sum a := by
    rw [Finset.sum_coe_sort (decS g a) (fun x => x)]; exact (decS_spec g a).1.2.2.2.2
  idem_prim τ x hx hc hxt := (decS_spec g _).2 _ τ.2 x hx hc hxt
  lab τ := labF g r e _ τ.1
  lab_spec τ := labF_spec g r e _ τ.1
  Rep a := Set ↥(decS g a)
  ofIrr τ := {τ}
  cons R τ := τ ∈ R
  cons_ofIrr _ _ := Set.mem_singleton_iff
  hc _ _ := ∅

open Classical in
theorem lzE_ser (hidem : ∀ f, e f * e f = e f) (hcen : ∀ f a, e f * a = a * e f)
    (horth : ∀ f f', f ≠ f' → e f * e f' = 0)
    (hsum : ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧
      ∑ f ∈ S, e f = 1) (f : (ZMod g)[X]) :
    e f = ∑ τ : (lzE g r e).Irr r, if (lzE g r e).lab τ = f then (lzE g r e).idem τ else 0 := by
  obtain ⟨T, hTm, hT⟩ := hsum
  have hmain : ∀ t ∈ decS g r, ∀ f, e f * t = if labF g r e r t = f then t else 0 := by
    intro t ht f
    obtain ⟨i, hi, hit, hj⟩ :=
      lab_unique (decS_spec g r).1 (decS_spec g r).2 e hidem hcen horth T hT ht
    have hlab : labF g r e r t = i := by
      have hex : ∃ f, LabQ g r e r t f := ⟨i, (hTm i).1 hi, fun h => by simp only [cast_eq]; exact hit⟩
      have hs := hex.choose_spec.2 rfl
      simp only [cast_eq] at hs
      unfold labF
      rw [dif_pos hex]
      by_contra hne
      exact (decS_spec g r).1.2.2.1 t ht (hs.symm.trans (hj _ hne))
    rw [hlab]
    split_ifs with hif
    · subst hif; exact hit
    · exact hj f (Ne.symm hif)
  show e f = ∑ τ : ↥(decS g r), if labF g r e r τ.1 = f then τ.1 else 0
  calc e f = e f * ∑ τ : ↥(decS g r), τ.1 := by
        rw [Finset.sum_coe_sort (decS g r) (fun x => x), (decS_spec g r).1.2.2.2.2, mul_one]
    _ = ∑ τ : ↥(decS g r), e f * τ.1 := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun τ _ => hmain τ.1 τ.2 f

end Lz

theorem exists_lz_serEq : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  intro D
  refine ⟨fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩;
    lzE (D.host.g k) D.R.r (D.ntypes.eSer k), ?_⟩
  intro k f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact lzE_ser _ _ _ (D.ntypes.eSer_idem k) (D.ntypes.eSer_central k) (D.ntypes.eSer_orth k)
    (D.ntypes.eSer_sum k) f

end GlobalTheory.LzExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotientStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_primePow_torsion_quotient : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  first | exact @GlobalTheory.GoodCoeff.exists_finset_pow_torsion | exact GlobalTheory.GoodCoeff.exists_finset_pow_torsion | (intros; apply GlobalTheory.GoodCoeff.exists_finset_pow_torsion <;> assumption)
end

