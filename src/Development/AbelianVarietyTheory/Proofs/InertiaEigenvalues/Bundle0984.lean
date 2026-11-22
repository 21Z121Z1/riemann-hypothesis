import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrime
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescGlue

open GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

theorem finite_of_overPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (hl : l.Prime)
    (S : Set (HeightOneSpectrum (𝓞 L))) (h : OverPrime l S) : S.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  show la.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact h la hla

theorem finite_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : S.Finite) : (below φ S).Finite := by
  have e : below φ S = ⋃ la ∈ S, {p : HeightOneSpectrum (𝓞 K) |
      p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)} := by
    ext p; simp [below]
  rw [e]
  exact hS.biUnion fun la _ => Set.Subsingleton.finite fun p1 h1 p2 h2 =>
    HeightOneSpectrum.ext (h1.trans h2.symm)

set_option maxHeartbeats 800000 in

theorem glue : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT h1 h2 h3 h4 h5 h6 i hVS hV hFP l hl C hC hPin S hS hUn φ hφmem hKf
    m x ψ hψ hφ hloc
  classical
  have hσ : ∀ t : T.Q.c.F, C.σ₂ (C.inc t) = T.σ₀ t := fun t => by
    rw [← RingHom.comp_apply, hC.1.2.2.1]
  have hfin : S.Finite := finite_of_overPrime l hl S hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    refine ⟨m, fun a => C.σ₂ (x a), ψ, fun a => ⟨x a, rfl, fun la h => absurd h (Set.notMem_empty la)⟩,
      fun a => ?_, hφ⟩
    obtain ⟨f, ⟨hf1, hf2⟩, hf⟩ := hψ a
    exact ⟨f, ⟨hf1, hf2, fun p hp => by
      obtain ⟨la, hla, _⟩ := hp
      exact absurd hla (Set.notMem_empty la)⟩, hf⟩
  set S' := hfin.toFinset with hS'
  have hmem : ∀ la : S', la.1 ∈ S := fun la => hfin.mem_toFinset.1 la.2
  choose m' x' ψ' hx' hψ' hφ' using fun la : S' => hloc la.1 (hmem la)
  choose a' ha' hav using fun (la : S') (a : Fin (m' la)) => hx' la a
  have hset : ∀ la : S', below C.inc {la.1} =
      {p | p.asIdeal = la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc)} := fun la => by
    ext p; simp [below]
  choose t ht htψ using fun (la : S') (a : Fin (m' la)) =>
    GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places D T hT i (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs h6.kap i)
      (la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc))
      (Ideal.IsPrime.comap _ (hK := la.1.isPrime)) (below C.inc S) (finite_below C.inc hfin) (ψ' la a)
      (hset la ▸ hψ' la a)
  have hte : ∀ (la : S') (a : Fin (m' la)), la.1.valuation _ (C.inc (t la a : T.Q.c.F)) = 1 := fun la a => by
    have e : C.inc (t la a : T.Q.c.F) = ((RingOfIntegers.mapRingHom C.inc (t la a) : 𝓞 C.d.c₂.F) : C.d.c₂.F) := rfl
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem la.1).mpr fun h => ht la a (Ideal.mem_comap.2 h)
  have ht0 : ∀ (la : S') (a : Fin (m' la)), T.σ₀ (t la a : T.Q.c.F) ≠ 0 := fun la a => by
    refine (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    rintro h0
    exact ht la a (h0 ▸ Ideal.zero_mem _)
  let Y : S' → Finset C.d.c₂.F := fun la => Finset.univ.image fun a => a' la a / C.inc (t la a : T.Q.c.F)
  have hY : ∀ la, ∀ y ∈ Y la, la.1.valuation _ y ≤ 1 := by
    intro la y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    rw [map_div₀, hte, div_one]
    exact hav la a la.1 (Set.mem_singleton _)
  have hne : S'.Nonempty := by
    obtain ⟨la, h⟩ := hSne
    exact ⟨la, hfin.mem_toFinset.2 h⟩
  obtain ⟨e, he1, he⟩ := GlobalTheory.exists_partition_one_integral_at_places _ S' hne Y hY
  let ι := Σ la : S', Fin (m' la)
  let ε := Fintype.equivFin ι
  let X : ι → ℂ := fun s => C.σ₂ (e s.1 * (a' s.1 s.2 / C.inc (t s.1 s.2 : T.Q.c.F)))
  let Ψ : ι → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ) := fun s => T.σ₀ (t s.1 s.2 : T.Q.c.F) • ψ' s.1 s.2
  have key : ∀ s : ι, X s • Ψ s = C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := by
    intro s
    simp only [X, Ψ, smul_smul, map_mul, map_div₀, hσ, ha']
    congr 1
    field_simp [ht0 s.1 s.2]
  refine ⟨Fintype.card ι, fun k => X (ε.symm k), fun k => Ψ (ε.symm k), fun k => ⟨_, rfl, fun la'' h'' =>
    he _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) la'' (hfin.mem_toFinset.2 h'')⟩,
    fun k => htψ _ _, ?_⟩
  symm
  calc ∑ k, X (ε.symm k) • Ψ (ε.symm k) = ∑ s : ι, X s • Ψ s := Equiv.sum_comp ε.symm (fun s => X s • Ψ s)
    _ = ∑ s : ι, C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := Finset.sum_congr rfl fun s _ => key s
    _ = ∑ la : S', ∑ a : Fin (m' la), C.σ₂ (e la) • (x' la a • ψ' la a) := Fintype.sum_sigma _
    _ = ∑ la : S', C.σ₂ (e la) • φ := Finset.sum_congr rfl fun la _ => by rw [← Finset.smul_sum, ← hφ' la]
    _ = φ := by rw [← Finset.sum_smul, ← map_sum, he1, map_one, one_smul]

end GlobalTheory.DescGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntFormDescentBelow
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem exists_local_basis {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {V : Type} [AddCommGroup V]
    [Module F V] (C : Submodule F V) [FiniteDimensional F C] (Int : V → Prop) (h0 : Int 0)
    (hadd : ∀ f g, Int f → Int g → Int (f + g)) (hsmul : ∀ (a : F) f, p.valuation F a ≤ 1 → Int f → Int (a • f))
    (hbd : ∀ f ∈ C, ∃ κ : F, κ ≠ 0 ∧ Int (κ • f)) {M : ℕ} (g : Fin M → V) (hg : ∀ i, g i ∈ C)
    (hgen : ∀ f ∈ C, Int f → ∃ o : Fin M → F, (∀ i, p.valuation F (o i) ≤ 1) ∧ f = ∑ i, o i • g i) :
    ∃ (m : ℕ) (β : Fin m → V), (∀ k, β k ∈ C ∧ Int (β k)) ∧ (∀ f ∈ C, ∃ c : Fin m → F, f = ∑ k, c k • β k) ∧
      ∀ c : Fin m → F, Int (∑ k, c k • β k) → ∀ k, p.valuation F (c k) ≤ 1 := by
  classical
  let B₀ := Module.finBasis F C
  choose κ hκ0 hκ using fun i => hbd (B₀ i : V) (B₀ i).2
  let B := B₀.unitsSMul fun i => Units.mk0 (κ i) (hκ0 i)
  have hB : ∀ i, ((B i : C) : V) = κ i • (B₀ i : V) := fun i => by
    simp [B, Module.Basis.unitsSMul_apply, Units.smul_def]
  let e : (Fin (Module.finrank F C) → F) →ₗ[F] V := C.subtype ∘ₗ (B.equivFun.symm : _ →ₗ[F] C)
  have heC : ∀ x, e x ∈ C := fun x => (B.equivFun.symm x).2
  have he1 : ∀ f : C, e (B.equivFun f) = f := fun f => by simp [e]
  have heinj : Function.Injective e := Subtype.val_injective.comp B.equivFun.symm.injective
  have hsingle : ∀ i, e (Pi.single i 1) = κ i • (B₀ i : V) := fun i => by
    rw [← hB, ← he1 (B i)]
    congr 1
    funext k
    simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  let S : Set (Fin (Module.finrank F C) → F) := {x | Int (e x)}
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun ki : Fin M × Fin (Module.finrank F C) => B.equivFun ⟨g ki.1, hg ki.1⟩ ki.2)
  have hvle : ∀ s : 𝓞 F, p.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := fun s => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact p.intValuation_le_one s
  obtain ⟨m, b, hbM, hbsp, hbli⟩ := GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi p _ S (by show Int (e 0); rw [map_zero]; exact h0)
    (fun x hx y hy => by show Int (e (x + y)); rw [map_add]; exact hadd _ _ hx hy)
    (fun a ha x hx => by show Int (e (a • x)); rw [map_smul]; exact hsmul _ _ ha hx)
    (fun i => by show Int (e _); rw [hsingle]; exact hκ i)
    ⟨algebraMap (𝓞 F) F d, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.coe_ne_zero d),
      fun x hx i => by
        obtain ⟨o, ho, hxo⟩ := hgen (e x) (heC x) hx
        have hx' : x = ∑ k, o k • B.equivFun ⟨g k, hg k⟩ := heinj (by
          rw [hxo, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, he1])
        rw [hx', Finset.sum_apply, Finset.mul_sum]
        refine Valuation.map_sum_le _ fun k _ => ?_
        obtain ⟨r, hr⟩ := hd (k, i)
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, map_mul, ← Algebra.smul_def]
        refine mul_le_one' (ho k) ?_
        rw [← hr]
        exact hvle r⟩
  refine ⟨m, fun k => e (b k), fun k => ⟨heC _, hbM k⟩, fun f hf => ?_, fun c hc k => ?_⟩
  · have hxsp : B.equivFun ⟨f, hf⟩ ∈ Submodule.span F (Set.range b) := by
      rw [← Finset.univ_sum_single (B.equivFun ⟨f, hf⟩)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Pi.single i (B.equivFun ⟨f, hf⟩ i) = B.equivFun ⟨f, hf⟩ i • (Pi.single i (1 : F) : Fin _ → F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨a, -, ha⟩ := hbsp (Pi.single i 1) (by show Int (e _); rw [hsingle]; exact hκ i)
      rw [ha]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hxsp
    refine ⟨c, ?_⟩
    have := he1 ⟨f, hf⟩
    rw [← hc, map_sum] at this
    exact this.symm.trans (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
  · have hy : (∑ k, c k • b k) ∈ S := by
      show Int (e _)
      convert hc using 1
      rw [map_sum]; exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    obtain ⟨a, ha, hya⟩ := hbsp _ hy
    have hz : ∑ k, (c k - a k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hya, sub_self]
    rw [sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hbli _ hz k)]
    exact ha k

theorem intForm_descent_below (l e : ℕ) (hl : l.Prime) : ∃ c₀ : ℕ, ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j →
    ∀ w : WeightFamilies.Wt D j, w.LastPos → Dom (wtA w) w.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) ''
      {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)}) →
    (∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h) →
    ∀ C : Cover T j T.σ₀, C.IsUnif → C.IsPinned (wtA w) w.n →
    ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)),
      la.asIdeal.comap (RingOfIntegers.mapRingHom C.inc) = p.asIdeal →
      ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → ((l : ℕ) : 𝓞 C.d.c₂.F) ∉ la.asIdeal ^ (e + 1) →
      ∀ φ ∈ C.intForms (wtA w) w.n {la}, (∀ k ∈ T.Kf j T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j T.σ₀) → ℂ)), (∀ i, la.valuation C.d.c₂.F (x i) ≤ 1) ∧
          (∀ i, ψ i ∈ baseInt T j T.σ₀ (wtA w) w.n {p}) ∧ ((l : ℂ) ^ c₀) • φ = ∑ i, C.σ₂ (x i) • ψ i := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.relative_different_order_bounded_absolute_ramification l e hl
  refine ⟨c, ?_⟩
  intro D T hL j hj w hlast hD hspan hK C hU hP la p hp0 hl1 hl2 φ hφ hφK
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  have hp : la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal := by
    rw [← hp0]; ext x; rfl
  have hσ := T.toCore.good_σ₀
  have hlp : ((l : ℕ) : 𝓞 T.Q.c.F) ∈ p.asIdeal := by
    rw [← hp0, Ideal.mem_comap, map_natCast]; exact hl1
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hfd := hL.cuspFD _ hj _ _ hD
  obtain ⟨M, g, hg, hgen⟩ := GlobalTheory.SupFinite.supSet_finitelyGenerated _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp
    hgood (wtA w) w.n hD hfd
  have hval := GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ (T.Q.Xo j) T.Q.c p
  obtain ⟨m, β, hβ, hspanβ, hprim⟩ := exists_local_basis p (cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n)
    (GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c p 1)
    ((hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top))
    (fun f g => GlobalTheory.GoodPtsModel.bddAll_add)
    (fun a f ha hf => by
      by_cases h0 : a = 0
      · subst h0
        rw [zero_smul]
        exact (hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top)
      have hv : (0 : ℤ) ≤ vLa p a := by
        have hne : p.valuation T.Q.c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
        have := (WithZero.log_le_log hne one_ne_zero).2 ha
        simp only [WithZero.log_one] at this
        simp only [vLa]; omega
      exact (GlobalTheory.GoodPtsModel.smul_mem_supSet (W := ⊤) hv ⟨trivial, hf⟩).2)
    (fun f hf => by
      obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp hgood (wtA w) w.n f hD hf
      exact ⟨κ, h1, (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 h2⟩)
    g (fun i => (hg i).1) (fun f hf hb => hgen f ⟨hf, hb⟩)
  have hβs : ∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
      rdU (T.U j T.σ₀) (β k) ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) := fun k =>
    ⟨cusp_le_sec _ _ _ _ _ (hβ k).1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ (wtA w) w.n ⟨β k, (hβ k).1⟩⟩
  obtain ⟨m', x, ψ, hψ, hφe⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hL j hj T.σ₀ hσ C hU _ _ hD hP hspan hK φ
    (C.intForms_subset _ _ _ hφ) hφK
  have hcc' : ∀ i, ∃ cc : Fin m → T.Q.c.F, ψ i = ∑ k, T.σ₀ (cc k) • T.phiJ j T.σ₀ (wtA w) (β k) := fun i => by
    obtain ⟨f, hf, hfe⟩ := hψ i
    obtain ⟨cc, hcc⟩ := hspanβ f (GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL j hj w hlast f hf.1 hf.2)
    refine ⟨cc, ?_⟩
    rw [← hfe, hcc]
    simp only [CoreJ.phiJ, map_sum, map_smulₛₗ, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  choose cc hcc using hcc'
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hU.2.2.1
  let y : Fin m → C.d.c₂.F := fun k => ∑ i, x i * C.inc (cc i k)
  have hsum : φ = ∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k) := by
    rw [hφe]
    simp only [y, hcc, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul, hσ₂]
    exact Finset.sum_comm
  have hφ' : (∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k)) ∈ C.intForms (wtA w) w.n {la} := hsum ▸ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.traceCombination_coverForm_integral_over_prime D T hL j hj T.σ₀ hσ _ _ hD hspan hK C hU hP la p hp m β hβs
    (fun k => (hval _).1 (hβ k).2) y hφ'
  have hdiff : ∀ k, ∀ d ∈ differentIdeal (𝓞 T.Q.c.F) (𝓞 C.d.c₂.F),
      la.valuation C.d.c₂.F (y k * (d : C.d.c₂.F)) ≤ 1 := fun k =>
    GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral T.Q.c.F C.d.c₂.F la p hp (y k)
      ⟨N, fun b hb => hprim (fun k => Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) ((hval _).2 (hN b hb)) k⟩
  have hcd := hc T.Q.c.F C.d.c₂.F p la hp hl1 hl2
  refine ⟨m, fun k => (l : C.d.c₂.F) ^ c * y k, fun k => T.phiJ j T.σ₀ (wtA w) (β k), ?_, ?_, ?_⟩
  · exact fun k => GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different l c T.Q.c.F C.d.c₂.F la hl1 hcd (y k) (hdiff k)
  · refine fun k => ⟨β k, ⟨(hβs k).1, (hβs k).2, fun q hq => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    exact (hval _).1 (hβ k).2
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_mul, map_pow, map_natCast]

end GlobalTheory.XiIntSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphHyp

theorem isSpherical_of_hypOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), NG.HypOutside J χ B → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v ∉ B → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → IsSpherical (GlobalTheory.LocLanglands.cls σ).rep := by
  intro L _ _ _ n a S hS J χ hlev B hB f hfiso hfT hf0 s hsB σ hσ
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  have hrt : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring,
      NG.rt L n κ f = (((1 : (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) →* ℂˣ) ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hU := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 h
    have hκB : TrivOutside Bᶜ κ := fun w hw => hκ w (by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm] at hw
      exact hsB (by simpa using hw))
    obtain ⟨hJ, hχ⟩ := hB κ hκB
    have hκJ := hJ.2 hU
    rw [hfT.2 ⟨κ, hκJ⟩, hχ hκJ]
    simp
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ i hi hic
    (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) 1 (fun g hg => hg)
    (by simp) f hfiso hf0 hrt
  have key : ∀ y, i y ∈ Formalism.UG.Ov L s.w → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (GlobalTheory.SphLoc.le_one_of_map i.toRingHom hi
      ((GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.w _).2 hy))
  have hfix : ∀ g ∈ KO (s.w.adicCompletion L) (Fin n), σ.ρ g u = u := by
    intro g hg
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion s.w n, GlobalTheory.HeckeScalarSph.mem_GLint_iff] at hg
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg' : g' ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
      rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
      refine ⟨fun p q => ?_, fun p q => ?_⟩
      · show Valued.v (i.symm (g.1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.1 p q)
      · rw [← map_inv]
        show Valued.v (i.symm ((g⁻¹).1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.2 p q)
    have e : Matrix.GeneralLinearGroup.map i.toRingHom g' = g :=
      Units.ext (Matrix.ext fun p q => i.apply_symm_apply _)
    have := hu g' hg'
    rw [e] at this
    simpa using this
  have hsph : IsSpherical σ.ρ := by
    intro h
    apply hu0
    have hm : u ∈ fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n)) := fun g => by
      simpa using hfix g.1 g.2
    rw [h] at hm
    exact hm
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ) hsph
end GlobalTheory.SphHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.LevelInv

theorem cast_mul {D : D7} {V W : HSp D} (e : V = W) (a b : GA D V) :
    cast (congrArg (GA D) e) (a * b) = cast (congrArg (GA D) e) a * cast (congrArg (GA D) e) b := by
  subst e
  rfl

theorem apply_eq_castDict {D : D7} {V W : HSp D} (e : V = W) (φ : GA D V → ℂ) (x : GA D V) :
    φ x = castDict e φ (cast (congrArg (GA D) e) x) := by
  subst e
  rfl

theorem thetaKO_mul_right {D : D7} {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (h : GA D V)
    (g κ : GA D W) (f : WO V W → ℂ) : thetaKO om h (g * κ) f = thetaKO om h g (om (1, κ) f) := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem ser_right_inv_levelK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (h : GA D (Vc D j)), h ∈ GfC (Vc D j) → ∀ (w : (Rl.cV j).W) (a : ℂ) (φ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ), castDict hV φ = (fun g => a * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w g) → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh w a φ hφ k hk g
  have hpb : T.pb = Rl.toRealDat.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev (hpins.2.tuple ()).half
  set k' : GA D (Wc D j) := cast (congrArg (GA D) hV) k with hk'def
  have hkk : cast (congrArg (GA D) hV.symm) k' = k := by rw [hk'def]; simp
  have hlift : Formalism.IndefR.Lev.IsLevelLift (Wc D j) (Rl.toRealDat.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k' :=
    (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV k').2 (by rw [hkk]; exact hk)
  have hv : Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.vP j A3.A.μ0) = (1 : ℂ) • Rl.toRealDat.vP j A3.A.μ0 := by
    have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar Rl.toRealDat hcore.lev hcore.models.inf hcore.thP.ωP hcore.thP.vP j A3.A.μ0 1 1 k'
      (GlobalTheory.RawLift.LevelFix.realDatum_identity_lifts_identity Rl.toRealDat j A3.A.μ0) hlift
    rw [e, GlobalTheory.RawLift.LevelFix.levChi_flag_one Rl.toRealDat j A3.A.μ0, inv_one]
  have hP : ∀ P, Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.ptP j A3.A.μ0 P) = Rl.toRealDat.ptP j A3.A.μ0 P := by
    intro P
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite Rl.toRealDat.ψ Rl.toRealDat.θ (Vc D j) (Wc D j) _ _
      (Rl.toRealDat.ωP j A3.A.μ0) hcore.models.inf (hcore.thP.ωP j A3.A.μ0) _ _ _ _ _ (hcore.thP.pt_theta j A3.A.μ0) 1
      (Subgroup.one_mem _) k' hlift.1 1 hv P
    exact this.trans (one_smul ℂ _)
  have hser : ∀ x, ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w (x * k') = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w x := by
    intro x
    rw [ser_vP, ser_vP, thetaKO_mul_right, hP]
  have e1 : φ (g * k) = castDict hV φ (cast (congrArg (GA D) hV) g * k') := by
    exact (apply_eq_castDict hV φ (g * k)).trans (congrArg (castDict hV φ) (cast_mul hV g k))
  have e2 : φ g = castDict hV φ (cast (congrArg (GA D) hV) g) := apply_eq_castDict hV φ g
  rw [e1, e2, hφ]
  exact congrArg (fun z => a * z) (hser _)

end GlobalTheory.SeriesTie.LevelInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspOfReading

set_option maxHeartbeats 1000000 in

theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw hn f hf hfh
  classical
  set S := T.cuspA j (wtA w) w.n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  let b' : Fin (Module.finrank T.Q.c.F S) → T.R j := fun i => (b i : T.R j)
  have hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b i).2
  have hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b') := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := S.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  by_contra hfS
  have hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) := by
    rw [linearIndependent_fin_cons]
    exact ⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩
  have hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := by
    intro i
    refine Fin.cases hf (fun i => ?_) i
    exact cusp_le_sec _ _ _ _ _ (b i).2
  have hC := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli
  have hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) :
      Fin (Module.finrank T.Q.c.F S + 1) → _) := by
    convert hC using 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  rw [linearIndependent_fin_cons] at hC'
  apply hC'.2
  have hspan := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hSb' hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.CuspOfReading
end

