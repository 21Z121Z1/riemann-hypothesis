import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0027
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {C : ACurve K} {V : Type} [AddCommGroup V] [Module K V]

theorem basis_mem {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) (q : Fin n) : b q ∈ L := by
  refine (h _).2 fun r => ?_
  by_cases e : q = r <;> simp [e, Finsupp.single_apply]

theorem smul_mem_lat {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) {a : K} (ha : C.v i a ≤ 1) {x : V} (hx : x ∈ L) : a • x ∈ L := by
  refine (h _).2 fun r => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' ha ((h _).1 hx r)

theorem v_det_le {i : C.I} {n : ℕ} {b b' : Module.Basis (Fin n) K V} {L L' : AddSubgroup V}
    (h : IsLatOf C i b L) (h' : IsLatOf C i b' L') (hle : L ≤ L') : C.v i (b'.det b) ≤ 1 := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine (C.v i).map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h' _).1 (hle (basis_mem h q)) _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

theorem deg_triv [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    {L : C.I → AddSubgroup V} (h : ∀ i, IsLatOf C i b (L i)) : IsBun C L ∧ deg C L = 0 := by
  have hb : IsBun C L := Inhab.isBun_of_basis C b L h
  refine ⟨hb, ?_⟩
  rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L n b (fun _ => b) hb h).2]
  simp [Module.Basis.det_self]

end SlopeTestRemainingChoices

theorem deg_mono : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  intro K _ C V _ _ _ L L' hL hL' hle
  choose b hb using hL.1
  choose b' hb' using hL'.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b hL hb
  obtain ⟨hf', e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L' _ (Module.finBasis K V) b' hL' hb'
  rw [e, e']
  refine finsum_le_finsum' (hf.subset fun i hi h1 => hi (by simp [h1]))
    (hf'.subset fun i hi h1 => hi (by simp [h1])) fun i => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  have n1 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have n2 : C.v i ((Module.finBasis K V).det (b' i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b' i)).ne_zero
  rw [WithZero.log_le_log n1 n2, ← Module.Basis.det_mul_det _ (b' i) (b i), map_mul]
  exact mul_le_of_le_one_right' (v_det_le (hb i) (hb' i) (hle i))

theorem deg_le_of_equiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i, ∀ x ∈ L i, e x ∈ L' i) : deg C L ≤ deg C L' := by
  obtain ⟨hM, hd⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C V V' L
    (fun i => (L i).comap e.symm.toLinearMap.toAddMonoidHom) e hL (fun i x => by simp)
  rw [← hd]
  refine deg_mono K C V' _ _ hM hL' fun i y hy => ?_
  simpa using h i (e.symm y) hy

theorem deg_inj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  intro K _ C V _ _ _ V' _ _ _ L L' f W hL hL' hf hh
  exact deg_le_of_equiv (Submodule.equivMapOfInjective f hf W) (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).1
    (GlobalTheory.T.sub_and_quotient_bundles K C V' L' _ hL').1 fun i x hx => hh i x hx

theorem subdeg_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  intro K _ C V _ _ _ n b L W h
  obtain ⟨hL, h0⟩ := deg_triv b h
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C V L W hL
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun q => W.mkQ (b q))
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range ((fun q => W.mkQ (b q)) ∘ a)) := by
    rw [hsp, show (Set.range fun q => W.mkQ (b q)) = W.mkQ '' Set.range b from
      Set.range_comp _ _, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  let c := (Module.Basis.mk hli htop).reindex (Fintype.equivFin κ)
  have hc : ∀ q, c q = W.mkQ (b (a ((Fintype.equivFin κ).symm q))) := fun q => by simp [c]
  obtain ⟨hM, hM0⟩ := deg_triv (C := C) c (fun i => Inhab.isLatOf_latOf C i c)
  have := deg_mono K C _ _ _ hM (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).2 fun i y hy => by
    rw [← c.sum_repr y]
    refine sum_mem fun q _ => ⟨c.repr y q • b (a ((Fintype.equivFin κ).symm q)),
      smul_mem_lat (h i) (hy q) (basis_mem (h i) _), ?_⟩
    rw [hc]; simp
  omega

theorem ses_restrict {K : Type} [Field K] {C : ACurve K} {V V' V'' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup V''] [Module K V''] [FiniteDimensional K V'']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} {L'' : C.I → AddSubgroup V''}
    {f : V →ₗ[K] V'} {g : V' →ₗ[K] V''} (hL' : IsBun C L') (h : ShortExact C L L' L'' f g)
    (A : Submodule K V) (X : Submodule K V') (B : Submodule K V'')
    (hA : ∀ x, x ∈ A ↔ f x ∈ X) (hB : ∀ z, z ∈ B ↔ ∃ y ∈ X, g y = z) :
    ∃ I : C.I → AddSubgroup B, IsBun C I ∧ subDeg C L' X = subDeg C L A + deg C I ∧
      ∀ i z, z ∈ I i ↔ ∃ y ∈ L' i, y ∈ X ∧ g y = z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  let f' : A →ₗ[K] X := f.restrict fun x hx => (hA x).1 hx
  let g' : X →ₗ[K] B := g.restrict fun y hy => (hB _).2 ⟨y, hy, rfl⟩
  have hse : ShortExact C (sub C L A) (sub C L' X)
      (fun i => (sub C L' X i).map g'.toAddMonoidHom) f' g' := by
    refine ⟨fun x y e => Subtype.ext (h1 (congrArg Subtype.val e)), fun y => ⟨fun hy => ?_, ?_⟩,
      fun z => ?_, fun i x => h4 i x, fun i z => Iff.rfl⟩
    · obtain ⟨x, hx⟩ := (h2 y).1 (congrArg Subtype.val hy)
      exact ⟨⟨x, (hA x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (h2.apply_apply_eq_zero x)
    · obtain ⟨y, hy, e⟩ := (hB z).1 z.2
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  obtain ⟨-, hI, hd⟩ := GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f' g' (GlobalTheory.T.sub_and_quotient_bundles K C V' L' X hL').1 hse
  refine ⟨_, hI, hd, fun i z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨y, hy, hX, e⟩
    exact ⟨⟨y, hX⟩, hy, Subtype.ext e⟩

theorem subdeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g X hL' h
  obtain ⟨I, hI, hd, hm⟩ := ses_restrict hL' h (X.comap f) X (X.map g) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl)
  have hL'' := (GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f g hL' h).2.1
  have : deg C I ≤ subDeg C L'' (X.map g) :=
    deg_mono K C _ _ _ hI (GlobalTheory.T.sub_and_quotient_bundles K C V'' L'' _ hL'').1 fun i z hz => by
      obtain ⟨y, hy, -, e⟩ := (hm i z).1 hz
      exact (h.2.2.2.2 i z).2 ⟨y, hy, e⟩
  omega

theorem exists_dot {K : Type} [Field K] {d : ℕ} (ψ : Module.Dual K (Fin d → K)) :
    ∃ u : Fin d → K, ∀ x, u ⬝ᵥ x = ψ x := by
  refine ⟨fun j => ψ (Pi.single j 1), fun x => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
  simp [dotProduct, mul_comm]

theorem subdeg_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  intro K _ C d L W X hL hW
  have hbij : Function.Bijective (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => funext fun j => ?_, fun ψ => ?_⟩
    · simpa using LinearMap.congr_fun hu (Pi.single j 1)
    · obtain ⟨u, hu⟩ := exists_dot ψ
      exact ⟨u, LinearMap.ext hu⟩
  obtain ⟨hD, -, hbi⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ L _ hL hbij
  let B₀ : (Fin d → K) →ₗ[K] W →ₗ[K] K := ((dotProductBilin K K).comp W.subtype).flip
  have hB₀ : ∀ φ (w : W), B₀ φ w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  let B : ((Fin d → K) ⧸ X) →ₗ[K] W →ₗ[K] K :=
    X.liftQ B₀ fun φ hφ => LinearMap.ext fun w => (hW w).1 w.2 φ hφ
  have hB : ∀ φ (w : W), B (X.mkQ φ) w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  have hBb : Function.Bijective B := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun ψ => ?_⟩
    · obtain ⟨φ, rfl⟩ := X.mkQ_surjective y
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_dot ψ
      have hu' : u ∈ W := (hW u).2 fun x hx => by
        rw [hu]; exact (Submodule.mem_dualAnnihilator ψ).1 hψ x hx
      rw [← hu, ← hB φ ⟨u, hu'⟩, hy]; rfl
    · obtain ⟨ψ', rfl⟩ := LinearMap.dualMap_surjective_of_injective W.injective_subtype ψ
      obtain ⟨u, hu⟩ := exists_dot ψ'
      refine ⟨X.mkQ u, LinearMap.ext fun w => ?_⟩
      rw [hB, dotProduct_comm, hu]; rfl
  obtain ⟨-, hq, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ _ B (GlobalTheory.T.sub_and_quotient_bundles K C _ _ X hD).2 hBb
  have he : dualLat C (quot C (dualLat C L (dotProductBilin K K)) X) B = sub C L W := by
    funext i; ext w
    have : (w : Fin d → K) ∈ L i ↔ (w : Fin d → K) ∈
        dualLat C (dualLat C L (dotProductBilin K K)) (dotProductBilin K K).flip i := by rw [hbi]
    refine Iff.trans ?_ this.symm
    constructor
    · intro H φ hφ
      exact H _ ⟨φ, hφ, rfl⟩
    · rintro H _ ⟨φ, hφ, rfl⟩
      exact H φ hφ
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C _ _ X hD
  rw [he] at hq
  unfold dotDual
  unfold subDeg at hs ⊢
  omega

end PositivityTheory.HtPt.Ch
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GdChartFin
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem chart_comp_zero : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y :=
  chart_comp_zero_of @PositivityTheory.HtPt.Gc.test_div @PositivityTheory.HtPt.Gc.test_descend @PositivityTheory.HtPt.Gb.red_omHT_bc

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
section
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem aeval_scale {σ K R A : Type} [Fintype K] [CommRing R] [CommRing A] [Algebra R A] (w : σ → K → ℕ)
    (c : K → A) (z : σ → A) {f : MvPolynomial σ R} {d : K → ℕ} (hf : IsWeightedHomogeneous w f d) :
    aeval (fun p => (∏ k, c k ^ w p k) * z p) f = (∏ k, c k ^ d k) * aeval z f := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, mul_add]
  | monomial m r hm =>
    rw [aeval_monomial, aeval_monomial, ← hm]
    have e : (∏ k, c k ^ (Finsupp.weight w m) k) = m.prod fun p n => (∏ k, c k ^ w p k) ^ n := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow,
        ← pow_mul, mul_comm]
      exact Finset.prod_comm
    rw [e]
    simp only [mul_pow, Finsupp.prod_mul]
    ring

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}

theorem ratio_eq [DecidableEq K] (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ = mseg y (Function.update s k i) / mseg y s := by
  have hk : y ⟨k, s k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  rw [div_eq_div_iff hk hs]
  unfold mseg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    Function.update_self]
  have e : ∏ j ∈ Finset.univ.erase k, y ⟨j, Function.update s k i j⟩ = ∏ j ∈ Finset.univ.erase k, y ⟨j, s j⟩ :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [e]
  ring

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem chartRing_mseg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) :
    chartRing o (mseg y) s = Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) := by
  classical
  refine le_antisymm (fun u hu => ?_) (Algebra.adjoin_le ?_)
  · have hk : ∀ k, y ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
    obtain ⟨n, U, hU, hv⟩ := GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) y (Pi.basisFun Ω (Fin 0))
      (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 s hs hu
    let c : Option (Option K) → Ω := fun b => b.elim 1 fun b' => b'.elim 1 fun k => y ⟨k, s k⟩
    let z : (Σ b, bundleIdx (bundleIdx J 0) 0 b) → Ω := fun p =>
      pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 p / c p.1
    have hc : ∀ b, c b ≠ 0 := by
      rintro (_ | _ | k)
      · exact one_ne_zero
      · exact one_ne_zero
      · exact hk k
    have h := aeval_scale _ c z hU
    have e1 : (fun p => (∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b) * z p) =
        pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 := by
      funext p
      have : ∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b = c p.1 := by
        rw [Finset.prod_eq_single p.1]
        · simp [blockWeight]
        · intro b _ hb
          simp [blockWeight, Pi.single_eq_of_ne hb]
        · simp
      rw [this]
      exact mul_div_cancel₀ _ (hc _)
    have e2 : ∏ b, c b ^ GenericProjClosureDivisor.vdeg (fun _ : K => n) b = segreVec y s ^ n := by
      simp [Fintype.prod_option, c, GenericProjClosureDivisor.vdeg, segreVec, Finset.prod_pow]
    rw [e1, e2, hv, Algebra.algebraMap_self_apply, mul_comm] at h
    have hu' : u = aeval z U := mul_left_cancel₀ (pow_ne_zero n hs) h
    have hz : aeval z U ∈ Algebra.adjoin o (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨U, rfl⟩
    rw [hu']
    refine Algebra.adjoin_mono ?_ hz
    rintro _ ⟨⟨_ | _ | k, i⟩, rfl⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact ⟨Function.update s k i, (ratio_eq y s hs k i).symm⟩
  · rintro _ ⟨j, rfl⟩
    exact div_mem_chartRing _ _ _

end PositivityTheory.HtPt.Hcptgen
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHtBc
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap]

end PositivityTheory.HtPt.Htat.HTBaseChange

open PositivityTheory.HtPt.Htat.HTBaseChange in

theorem PositivityTheory.HtPt.Htat.ht_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← valAt_comp_top, ← hσj', valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := PositivityTheory.HtPt.Htat.ht_linear R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (dualMap (qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [dualMap, qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [dualMap, qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← valAt_comp_top, h1, valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [dualMap, qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.LevMapLev
section
noncomputable section

namespace PositivityTheory.HtPt.Gi

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra
  PositivityTheory.HtPt.Twpdiv

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
    rintro _ ⟨b, rfl⟩
    exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] {X : OrdTower p O La L} {G : PDivGroup p O}
  (e : ∀ n, G.A n ≃ₐ[O] X.A n) {τ : La →+ G.Tate}

def evG (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : evG e n t g = (e n g).1 t := rfl

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem sepG (n : ℕ) : Sep (evG e n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))

variable {e}

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_lev (hre : X.Realises G e τ) (n : ℕ) (a : La) : evG e n (lev p n a) = (τ a).pt n :=
  AlgHom.ext fun g => (hre.pt a n g).symm

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_one (hre : X.Realises G e τ) (n : ℕ) (g : G.A n) : evG e n 1 g = counit (R := O) g := by
  rw [← lev_zero, evG_lev hre, map_zero]
  rfl

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_mul (hre : X.Realises G e τ) (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
    pair (evG e n s) (evG e n t) (comul (R := O) g) = evG e n (s * t) g := by
  obtain ⟨a, rfl⟩ := lev_surjective p n s
  obtain ⟨b, rfl⟩ := lev_surjective p n t
  rw [← lev_add, evG_lev hre, evG_lev hre, evG_lev hre, map_add]
  exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm

def pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) : G.A n →ₐ[O] G.A n :=
  Ord.liftTo (evG e n) (sepG e n) (fun t => evG e n (levMap p n φ t)) fun g =>
    ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), (h n (e n g).1 _ fun _ => rfl).1 (e n g).2⟩, fun t => by
      rw [evG_apply, AlgEquiv.apply_symm_apply]; rfl⟩

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) :
    (evG e n t).comp (pullA (e := e) h n) = evG e n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA' {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
    evG e n t (pullA (e := e) h n g) = evG e n (levMap p n φ t) g := DFunLike.congr_fun (evG_pullA h n t) g

def pullB (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) :
    G.A n →ₐc[O] G.A n :=
  BialgHom.ofAlgHom (pullA (e := e) h n)
    (AlgHom.ext fun g => by
      change counit (R := O) (pullA (e := e) h n g) = counit (R := O) g
      rw [← evG_one hre, ← evG_one hre, evG_pullA', map_one])
    (AlgHom.ext fun g => (sepG e n).pair (sepG e n) _ _ fun z => by
      change pair _ _ (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
        pair _ _ (comul (R := O) (pullA (e := e) h n g))
      rw [pair_map, evG_pullA, evG_pullA, evG_mul hre, evG_mul hre, evG_pullA', map_mul])

def endG (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) : G ⟶ G where
  app := pullB hre h
  comm n := BialgHom.ext fun g => sepG e n _ _ fun t => by
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    change (e n (G.res n (pullA (e := e) h (n + 1) g))).1 _ = evG e n _ (pullA (e := e) h n (G.res n g))
    rw [hre.res, evG_pullA', levMap_lev, evG_apply, hre.res, ← evG_apply, evG_pullA', levMap_lev, map_nsmul,
      evG_apply]

end PositivityTheory.HtPt.Gi

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Gi.tower_end : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  refine ⟨fun φ dφ h => ⟨PositivityTheory.HtPt.Gi.endG hre h, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_),
    fun n g a => PositivityTheory.HtPt.Gi.evG_pullA' h n _ g⟩, fun H f f' hf => hom_ext fun n => BialgHom.ext fun g =>
      PositivityTheory.HtPt.Gi.sepG e n _ _ fun t => ?_⟩
  · rw [tateMap_pt, ← PositivityTheory.HtPt.Gi.evG_lev hre, ← PositivityTheory.HtPt.Gi.evG_lev hre]
    exact PositivityTheory.HtPt.Gi.evG_pullA' h n _ g
  · obtain ⟨a, rfl⟩ := PositivityTheory.HtPt.Twpdiv.lev_surjective p n t
    rw [PositivityTheory.HtPt.Gi.evG_lev hre, ← tateMap_pt, ← tateMap_pt, hf]
end

