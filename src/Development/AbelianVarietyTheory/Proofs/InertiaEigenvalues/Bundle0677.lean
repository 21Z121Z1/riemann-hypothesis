import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CentralSupport

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _

theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow {α : Type} (S : Finset α) (c : α → ℂ) : ∏ a ∈ S, absPow k (c a) = absPow k (∑ a ∈ S, c a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, absPow_add]

theorem absPow_pow (s : ℂ) (N : ℕ) (z : kˣ) : absPow k s (z ^ N) = absPow k (N * s) z := by
  ext
  rw [map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow, Complex.cpow_nat_mul]

theorem deltaHalf_scalar {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) : deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have hd : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) := fun a => by
    ext; simp [GeneralLinearGroup.scalar]
  rw [deltaHalf_apply]
  simp only [hd, absPow_pow]
  rw [← MonoidHom.finsetProd_apply, prod_absPow]
  have h0 : ∑ a, ((Fintype.card (m a) : ℕ) : ℂ) * ((modExp m a : ℂ) / 2) = 0 := by
    have := congrArg (fun t : ℤ => (t : ℂ) / 2) (sum_card_mul_modExp m)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, zero_div, Finset.sum_div] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h0, absPow_zero, MonoidHom.one_apply]

theorem hasCentralChar_multiProd_prod {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (ω : α → kˣ →* ℂˣ)
    (hω : ∀ a, HasCentralChar (σ a) (ω a)) : HasCentralChar (multiProd e σ) (∏ a, ω a) := by
  intro z f
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (c a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hb]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hb]
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (fun a => GeneralLinearGroup.scalar (c a) z)⟩
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h5 := h4 x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar σ _ (fun a => (ω a z : ℂ)) (fun a => hω a z)] at h5
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = ((∏ a, ω a) z : ℂ) • f.1.1 x
  rw [hc, ← h1, MonoidHom.finsetProd_apply, Units.coe_prod]
  simpa using h5

theorem centralChar_eq_prod_support : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s : Multiset (IrrGL k))
    (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL k → kˣ →* ℂˣ,
      (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  intro _ k _ _ _ _ _ x s ω hs hω
  choose f _ hf using fun y : IrrGL k => LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  refine ⟨f, fun y _ => hf y, fun z => ?_⟩
  obtain ⟨h, x', rfl, hi, -, e, hsub⟩ := hs
  have hcen := hasCentralChar_multiProd_prod e (fun a => (x' a).rep) (fun a => f (x' a)) (fun a => hf (x' a))
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
  rw [hω] at h1
  have h2 := smul_left_injective ℂ hv h1
  rw [Multiset.map_map]
  change ω z = ∏ a, f (x' a) z
  apply Units.ext
  rw [h2, MonoidHom.finsetProd_apply]

end GlobalTheory.CentralSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDeRhamOfCoboundarySemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem cocycle_dies_dR_of_dies_st : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  intro l _ P AI T K V _ _ ρ c z hz
  obtain ⟨ι, hC, hEq⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hst, -, hone⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hC hEq K V ρ
  refine ⟨LinearMap.lTensor V ι.toLinearMap z, fun g => ?_⟩
  rw [← hone (c g), hz g, map_sub, hst g z]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlaces
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompositumCompletion

theorem exists_completion_map {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    (jL : L →+* L') (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L'))
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) :
    ∃ μ : v.adicCompletion L →+* v'.adicCompletion L', Continuous μ ∧
      ∀ x, μ (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  letI : Algebra L L' := jL.toAlgebra
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨by ext x; exact (h x).symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver L L' v v').continuous
  let φ : v.adicCompletion L →+* v'.adicCompletion L' :=
    ((HeightOneSpectrum.adicCompletion.equiv L' v').symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L'))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  refine ⟨φ, ?_, fun x => ?_⟩
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' v').comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L')))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  · apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)

theorem exists_ringEquiv_completion : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  intro E L E' L' _ _ _ _ _ _ _ _ _ _ w v w' v' j jL i hv hv' hjv hjL hadj hic hij
  obtain ⟨κ, hκc, hκ⟩ := exists_completion_map (algebraMap E L) w v (fun x => hv x)
  obtain ⟨κ', hκ'c, hκ'⟩ := exists_completion_map (algebraMap E' L') w' v' (fun x => hv' x)
  obtain ⟨μ, hμc, hμ⟩ := exists_completion_map jL v v' hjv
  have hcomm : ∀ a, μ (κ a) = κ' (i a) := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (hμc.comp hκc) (hκ'c.comp hic)
      (funext fun x => by simp only [Function.comp_apply, hκ, hμ, hjL, hij, hκ'])) a
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := E) (M := L)
  have hrange : Set.range jL ⊆ Submodule.span E' (jL '' (s : Set L)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span E (s : Set L) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul, hjL, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha
  have htop : Submodule.span E' (Set.range jL) = ⊤ := by
    have h1 := Algebra.adjoin_eq_span E' (Set.range jL)
    rw [hadj, Algebra.top_toSubmodule] at h1
    have hcl : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL :=
      congrArg SetLike.coe (Submonoid.closure_eq (MonoidHom.mrange jL))
    rw [h1, hcl]
  have hspan : ∀ y : L', y ∈ Submodule.span E' (jL '' (s : Set L)) := fun y => by
    have hy : y ∈ Submodule.span E' (Set.range jL) := htop ▸ Submodule.mem_top
    exact (Submodule.span_le.2 hrange) hy
  letI : Algebra (w'.adicCompletion E') (v'.adicCompletion L') := κ'.toAlgebra
  haveI : ContinuousSMul (w'.adicCompletion E') (v'.adicCompletion L') :=
    continuousSMul_of_algebraMap _ _ hκ'c
  letI : NontriviallyNormedField (w'.adicCompletion E') := Valued.toNontriviallyNormedField _ _
  let M : Submodule (w'.adicCompletion E') (v'.adicCompletion L') :=
    Submodule.span _ ((fun y => algebraMap L' (v'.adicCompletion L') (jL y)) '' (s : Set L))
  haveI : FiniteDimensional (w'.adicCompletion E') M :=
    FiniteDimensional.span_of_finite _ (s.finite_toSet.image _)
  have hcl : IsClosed (M : Set (v'.adicCompletion L')) := Submodule.closed_of_finiteDimensional _
  have hM : ∀ y : L', algebraMap L' (v'.adicCompletion L') y ∈ M := fun y => by
    induction hspan y using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : algebraMap L' (v'.adicCompletion L') (c • a) =
          (algebraMap E' (w'.adicCompletion E') c) • algebraMap L' (v'.adicCompletion L') a := by
        rw [Algebra.smul_def c a, map_mul, ← hκ']; rfl
      rw [e]; exact Submodule.smul_mem _ _ ha
  have hMμ : ∀ z ∈ M, z ∈ Set.range μ := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, _, rfl⟩ := hz
      exact ⟨algebraMap L _ x, hμ x⟩
    | zero => exact ⟨0, map_zero μ⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' + b', map_add μ a' b'⟩
    | smul c a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨κ (i.symm c) * a', by rw [map_mul, hcomm, i.apply_symm_apply]; rfl⟩
  have hsurj : Function.Surjective μ := fun y => by
    have hy : y ∈ (M : Set (v'.adicCompletion L')) :=
      (HeightOneSpectrum.denseRange_algebraMap L' v').induction_on
        (p := fun y => y ∈ (M : Set (v'.adicCompletion L'))) y hcl hM
    exact hMμ y hy
  exact ⟨RingEquiv.ofBijective μ ⟨μ.injective, hsurj⟩, hμc, fun x => hμ x⟩

end GlobalTheory.CompositumCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHecke_conjugatePlace_petersson_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by
  first | exact @GlobalTheory.CxHeckeAdj.hecke_adjoint | exact GlobalTheory.CxHeckeAdj.hecke_adjoint | (intros; apply GlobalTheory.CxHeckeAdj.hecke_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem conv_single_prod_eq_zero {ι : Type} [Fintype ι] {Γ : ι → Type} [∀ i, Group (Γ i)]
    [∀ i, Finite (Γ i)] (G : Type) [Group G] [Fintype G] (eR : G ≃* (∀ i, Γ i)) (i0 : ι)
    (M : MonoidAlgebra ℂ (Γ i0)) (E : ∀ i, MonoidAlgebra ℂ (Γ i)) (hM : M * E i0 = 0) (x : G) :
    ∑ y : G, (open Classical in if ∀ i, i ≠ i0 → eR y i = 1 then M.coeff (eR y i0) else 0) *
      ∏ i, (E i).coeff (eR (y⁻¹ * x) i) = 0 := by
  classical
  haveI : Fintype (Γ i0) := Fintype.ofFinite _
  have hinj : Function.Injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) :=
    eR.symm.injective.comp (Pi.mulSingle_injective i0)
  rw [← Fintype.sum_of_injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) hinj
    (fun z => (M.coeff z * (E i0).coeff (z⁻¹ * eR x i0)) *
      ∏ i ∈ Finset.univ.erase i0, (E i).coeff (eR x i))]
  · rw [← Finset.sum_mul]
    have h := MonoidAlgebra.coeff_mul_apply_left M (E i0) (eR x i0)
    rw [hM, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h]; simp
  · intro y hy
    rw [if_neg, zero_mul]
    intro h
    apply hy
    refine ⟨eR y i0, ?_⟩
    simp only
    rw [MulEquiv.symm_apply_eq]
    funext i
    by_cases hi : i = i0
    · subst hi; simp
    · rw [Pi.mulSingle_eq_of_ne hi, h i hi]
  · intro z
    rw [if_pos, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), mul_assoc]
    · congr 1
      · simp
      · congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hi' := Finset.ne_of_mem_erase hi
          simp [Pi.mulSingle_eq_of_ne hi']
    · intro i hi
      simp [Pi.mulSingle_eq_of_ne hi]

theorem conv_single_goodProj_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  intro D G _ _ eR kv0 M hM x
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) :=
    Fintype.ofFinite _
  have he : ∀ g : G0g D.nd, D.ntypes.e0.coeff g =
      ∑ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := by
    intro g
    rw [← finsum_eq_sum_of_fintype]
    rfl
  simp only [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with ha
  · haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    have := conv_single_prod_eq_zero (Γ := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      G eR kv0 M (fun kv => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) (hM a ha) x
    convert this
  · simp

end GlobalTheory.DownLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem countable_numberField_type (K : Type) [Field K] [NumberField K] : Countable K := by
  let b := Module.finBasis ℚ K
  exact (b.equivFun.toEquiv.injective).countable

theorem lag_countable : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  intro D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  let M := (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)
  haveI : Countable (Submodule D.host.E M) := by
    have hs : Function.Surjective (fun s : Finset M => Submodule.span D.host.E (s : Set M)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  unfold Lag
  infer_instance

end GlobalTheory.RawLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.BadPlace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def datP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (e : AE D) : WO (Vc D i) (Wc D i) → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
      omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
    else 0

end GlobalTheory.BadPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteSpaceFormsFunctionalPrincipalType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DefiniteType

theorem adForms_mul {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (f : G → W) (hf : f ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ)
    (h : G) (k : G) (hk : k ∈ J) : f (h * k) = (χ ⟨k, hk⟩ : ℂ) • f h := by
  have h1 : f (ι 1 * h * k) = (χ ⟨k, hk⟩ : ℂ) • ρ 1 (f h) := hf 1 h ⟨k, hk⟩
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at h1

theorem fin_mem {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).J :=
  hκ.2

theorem chi_eq {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hk : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J) :
    (((levEnv V β L).χ ⟨_, hk⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ :=
  rfl

theorem ext_mul {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Formalism.IndefR.Bridge.Gf V → c.W) (κ : GA D V) (hκ : κ ∈ GfC V) (h : GA D V)
    (z : ℂ) (hz : f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ) = z • f ((finHom V).rangeRestrict h)) :
    c.ext f (h * κ) = z • c.ext f h := by
  have h3 : c.ρ κ⁻¹ = 1 := hc.1 _ ((GfC V).inv_mem hκ)
  have h4 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, c.ρ.map_mul, h3, one_mul]
  have h5 : f ((finHom V).rangeRestrict (h * κ)) = z • f ((finHom V).rangeRestrict h) :=
    (congrArg f ((finHom V).rangeRestrict.map_mul h κ)).trans hz
  show c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) = z • c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  rw [h4, h5, map_smul]

theorem ext_mul_lev {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (f : Formalism.IndefR.Bridge.Gf V → c.W)
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * κ) = levChi V β (flag1L L) κ • c.ext f h :=
  ext_mul c hc f κ hκ.1 h _ (chi_eq β L κ (fin_mem β L κ hκ) ▸
    adForms_mul (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ f hf _ _ (fin_mem β L κ hκ))

theorem hasType_extV : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ),
      HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i t y l κ hκ h
  have hm := (hc.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have h1 := ext_mul_lev (R.cV i) (hc.models.cV i) (R.βV i) (R.datVt i t) ((R.HV i t).e y) hm κ hκ h
  exact (congrArg l h1).trans (map_smul l _ _)

end GlobalTheory.DefiniteType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponentStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_exists_localComponent : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  first | exact @GlobalTheory.DiscLocEx.exists_isLocCompGL | exact GlobalTheory.DiscLocEx.exists_isLocCompGL | (intros; apply GlobalTheory.DiscLocEx.exists_isLocCompGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitarisStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N), IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  first | exact @GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | exact GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | (intros; apply GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL <;> assumption)
end

