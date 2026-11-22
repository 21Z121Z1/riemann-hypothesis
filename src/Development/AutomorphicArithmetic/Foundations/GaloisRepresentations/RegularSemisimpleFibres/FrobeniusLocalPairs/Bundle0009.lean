import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
import GroundTheory.LocalFields.Uniqueness
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchOfSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TraceRangeEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TwScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.CuspidalAdmissibility.OccursIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Derive
section
noncomputable section

open ValuativeRel

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem mem_int' (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  have hx := x.2
  rw [Valuation.mem_integer_iff] at hx ⊢
  rwa [GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

private theorem pow_red' (h : IsRes rk rK s sb) (j : ℕ) (x y : 𝒪[K]) (hy : (y : K) = (s ^ j) x) :
    rK y = (sb ^ j) (rK x) := by
  induction j generalizing y with
  | zero =>
    have hyx : y = x := Subtype.ext (by simpa using hy)
    subst hyx
    simp
  | succ j ih =>
    let z : 𝒪[K] := ⟨(s ^ j) x, mem_int' (s ^ j) x⟩
    have hz : rK z = (sb ^ j) (rK x) := ih z rfl
    have hyz : (y : K) = s (z : K) := by
      rw [hy, pow_succ']
      rfl
    rw [h.gal z y hyz, hz, pow_succ']
    rfl

private theorem finrank_dvd' [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  classical
  haveI : Algebra.IsAlgebraic F₀ F₁ := Algebra.IsAlgebraic.of_finite F₀ F₁
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z]
    rfl
  have hone : sb ^ orderOf s = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := h.onto₁ w
    have := pow_red' h (orderOf s) x x (by rw [pow_orderOf_eq_one]; rfl)
    rw [AlgEquiv.one_apply, ← this]
  rw [← h.deg, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁, ← hsb]
  exact orderOf_dvd_of_pow_eq_one hone

private theorem isGalois_of_isRes [Fintype F₁] (h : IsRes rk rK s sb) : IsGalois k K := by
  classical
  have hd := finrank_dvd' h
  have hpos : 0 < orderOf s := orderOf_pos s
  have hle1 : orderOf s ≤ Fintype.card (K ≃ₐ[k] K) := orderOf_le_card_univ
  have hle2 : Fintype.card (K ≃ₐ[k] K) ≤ Module.finrank k K := AlgEquiv.card_le
  have hle3 : Module.finrank k K ≤ orderOf s := Nat.le_of_dvd hpos hd
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.derive :
    UpperTheory.Gal.InertialTypesAlt.L.Derive := by
  intro k K _ _ _ _ _ _ _ _ _ hc F₀ F₁ _ _ _ _ _ rk rK s sb h
  haveI hv : ValuativeExtension k K := GlobalTheory.LBC.Inh.valuativeExtension hc
  have hpos : 0 < Module.finrank k K := by
    rw [← h.deg]
    exact Module.finrank_pos
  haveI hf : FiniteDimensional k K := Module.finite_of_finrank_pos hpos
  exact ⟨hv, hf, isGalois_of_isRes h⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

section Gen

variable {G H Γ V : Type} [Group G] [Group H] [Group Γ] [AddCommGroup V] [Module ℂ V]

private theorem mem_fx (ρ : Representation ℂ G V) (U : Subgroup G) (v : V) :
    v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  show (∀ h : U, ρ h v = ((1 : U →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u u.2⟩

private theorem fx_stable (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (y : H) {v : V}
    (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v ∈ fixed ρ (p.ker.map ι) := by
  rw [mem_fx] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hk0 : p k = 1 := hk
  have hk' : y⁻¹ * k * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, hk0, mul_one, map_inv, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk', rfl⟩
  calc ρ (ι k) (ρ (ι y) v) = ρ (ι (k * y)) v := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι (y * (y⁻¹ * k * y))) v := by congr 2; group
    _ = ρ (ι y) (ρ (ι (y⁻¹ * k * y)) v) := by rw [map_mul ι y, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y) v := by rw [hfix]

private theorem fx_eq (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) {y y' : H} (h : p y = p y')
    {v : V} (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v = ρ (ι y') v := by
  rw [mem_fx] at hv
  have hk : y'⁻¹ * y ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk, rfl⟩
  calc ρ (ι y) v = ρ (ι (y' * (y'⁻¹ * y))) v := by rw [mul_inv_cancel_left]
    _ = ρ (ι y') (ρ (ι (y'⁻¹ * y)) v) := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y') v := by rw [hfix]

private def rp (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p) :
    Representation ℂ Γ (fixed ρ (p.ker.map ι)) where
  toFun g := (ρ (ι (Function.surjInv hp g))).restrict fun _ hv => fx_stable ρ ι p _ hv
  map_one' := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp 1) = p 1 := by simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv
  map_mul' a b := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp (a * b)) = p (Function.surjInv hp a * Function.surjInv hp b) := by
      simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv

private theorem rp_spec (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p)
    (y : H) (x : fixed ρ (p.ker.map ι)) : (rp ρ ι p hp (p y) x : V) = ρ (ι y) x := by
  show ρ (ι (Function.surjInv hp (p y))) x = _
  exact fx_eq ρ ι p (Function.surjInv_eq hp (p y)) x.2

private theorem rel_eq (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (hp : Function.Surjective p) :
    (p.ker.map ι).relIndex ι.range = Nat.card Γ := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι, Subgroup.relIndex_top_right,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr hp]
  exact Subgroup.card_top

private theorem lev_eq_lemma (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (a b : H) :
    ((ι a : G) : G ⧸ p.ker.map ι) = ((ι b : G) : G ⧸ p.ker.map ι) ↔ p a = p b := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨k, hk, hke⟩
    have hk0 : p k = 1 := hk
    have hkb : k = a⁻¹ * b := hι (by rw [hke, map_mul, map_inv])
    rw [hkb, map_mul, map_inv, inv_mul_eq_one] at hk0
    exact hk0
  · intro h
    refine ⟨a⁻¹ * b, ?_, by rw [map_mul, map_inv]⟩
    show p (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]

private theorem exists_quotient_out_eq_and_eq_of_map_ker (ι : H →* G) (p : H →* Γ) (y : H) :
    ∃ z, Quotient.out ((ι y : G) : G ⧸ p.ker.map ι) = ι z ∧ p z = p y := by
  obtain ⟨⟨u, k, hk, rfl⟩, hu⟩ := QuotientGroup.mk_out_eq_mul (p.ker.map ι) (ι y)
  have hk0 : p k = 1 := hk
  exact ⟨y * k, by simp [hu], by rw [map_mul, hk0, mul_one]⟩

private theorem lev_eq [Fintype Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V) {x : V} (hx : A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A x =
      (Nat.card Γ : ℂ)⁻¹ • ∑ g : Γ, fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
  classical
  let φ : Γ → G ⧸ p.ker.map ι := fun g => ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)
  have hφ : Function.Injective φ := by
    intro g g' h
    have h2 := (lev_eq_lemma ι hι p _ _).1 h
    rwa [Function.surjInv_eq hp, Function.surjInv_eq hp] at h2
  have hsupp : Function.support (fun q : G ⧸ p.ker.map ι => f (Quotient.out q) • ρ (Quotient.out q) ∘ₗ A) ⊆
      (Finset.univ.image φ : Set (G ⧸ p.ker.map ι)) := by
    intro q hq
    by_contra hn
    apply hq
    have hf : f (Quotient.out q) = 0 := by
      apply hf0
      intro hr
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hr
      apply hn
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p y, Finset.mem_univ _, ?_⟩)
      rw [← QuotientGroup.out_eq' q, ← hy]
      exact (lev_eq_lemma ι hι p _ _).2 (Function.surjInv_eq hp _)
    simp [hf]
  have hterm : ∀ g, f (Quotient.out (φ g)) • ρ (Quotient.out (φ g)) (A x) =
      fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
    intro g
    obtain ⟨z, hz, hpz⟩ := exists_quotient_out_eq_and_eq_of_map_ker ι p (Function.surjInv hp g)
    show f (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) •
      ρ (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) (A x) = _
    rw [hz, hf1, hpz, Function.surjInv_eq hp]
    congr 1
    exact fx_eq ρ ι p hpz hx
  unfold GlobalTheory.BCT.levOp
  rw [rel_eq ι hι p hp, LinearMap.smul_apply, finsum_eq_sum_of_support_subset _ hsupp, LinearMap.sum_apply,
    Finset.sum_image (fun a _ b _ h => hφ h)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  exact hterm g

private theorem tr_eq [Finite Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (p.ker.map ι), A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.twTr ρ ι.range (p.ker.map ι) f A =
      (Nat.card Γ : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (rp ρ ι p hp g ∘ₗ A.restrict hA)) := by
  haveI := Fintype.ofFinite Γ
  have hL : ∀ v ∈ fixed ρ (p.ker.map ι),
      GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A v ∈ fixed ρ (p.ker.map ι) := by
    intro v hv
    rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
    exact fx_stable ρ ι p _ (hA v hv)
  unfold GlobalTheory.BCT.twTr
  rw [dif_pos hL, finsum_eq_sum_of_fintype, ← smul_eq_mul, ← map_smul]
  congr 1
  ext ⟨v, hv⟩
  simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_smul, Submodule.coe_sum]
  rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
  rfl

end Gen

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {F₀ : Type} [Field F₀]

private theorem iota_inj (n : ℕ) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
  intro a b h
  ext i j
  have h2 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h
  simpa using h2

private theorem unit_of_ne (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) {x : 𝒪[k]} (hx : rd x ≠ 0) :
    IsUnit x := by
  by_contra hu
  apply hx
  have hmax := RingHom.ker_isMaximal_of_surjective rd hrd
  have hm : x ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal x).2 hu
  rw [← IsLocalRing.eq_maximalIdeal hmax] at hm
  exact (RingHom.mem_ker).1 hm

private theorem gl_onto (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (n : ℕ) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) rd) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => Function.surjInv hrd ((g : Matrix (Fin n) (Fin n) F₀) i j)
  have hM : M.map rd = (g : Matrix (Fin n) (Fin n) F₀) := by
    ext i j
    rw [Matrix.map_apply]
    exact Function.surjInv_eq hrd _
  have hdet : IsUnit M.det := by
    apply unit_of_ne rd hrd
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  refine ⟨Matrix.nonsingInvUnit M hdet, ?_⟩
  ext i j
  show rd (M i j) = _
  exact Function.surjInv_eq hrd _

private theorem infl_on (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y', GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' = GeneralLinearGroup.map (algebraMap 𝒪[k] k) y :=
    ⟨y, rfl⟩
  unfold infl
  rw [dif_pos h, iota_inj (k := k) n h.choose_spec]

private theorem infl_off (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (x : GL (Fin n) k)
    (hx : x ∉ (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)).range) : infl rd fb x = 0 := by
  unfold infl
  rw [dif_neg (fun h => hx (MonoidHom.mem_range.2 h))]

end Loc

end UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

open UpperTheory.Gal.InertialTypesAlt.L.FiniteActions in
theorem UpperTheory.Gal.InertialTypesAlt.L.finAct :
    UpperTheory.Gal.InertialTypesAlt.L.FinAct := by
  intro k _ _ _ _ F₀ _ _ rd hrd n V _ _ ρ
  have hp := gl_onto rd hrd n
  refine ⟨fun g => hp g, rp ρ _ _ hp, fun y x => rp_spec ρ _ _ hp y x, fun fb A hA => ?_⟩
  exact tr_eq ρ _ (iota_inj n) _ hp (infl rd fb) fb (infl_on rd fb) (infl_off rd fb) A hA
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinety
section
theorem UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra :
    UpperTheory.Gal.InertialTypesAlt.L.FrobeniusTwistedHilbertNinety := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hd c hc
  classical
  have hfrob : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hsb]
  have hgen : ∀ t : F₁ ≃ₐ[F₀] F₁, t ∈ Subgroup.zpowers sb := by
    intro t
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F₀ F₁).2 t
    rw [← hi, ← hfrob]
    exact Subgroup.npow_mem_zpowers _ _
  have hG : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁) := UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb hgen
  let S : Subring A := (τ : A →+* A).eqLocus (RingHom.id A)
  let f : F₀ →+* S := ((algebraMap F₁ A).comp (algebraMap F₀ F₁)).codRestrict S (fun z => by
    change τ (algebraMap F₁ A (algebraMap F₀ F₁ z)) = algebraMap F₁ A (algebraMap F₀ F₁ z)
    rw [hτ, AlgEquiv.commutes])
  letI : Algebra F₀ S := f.toAlgebra
  haveI : Module.Finite F₀ S := Module.Finite.of_finite
  let σ : A ≃ₐ[S] A := AlgEquiv.ofRingEquiv (f := τ) (fun r => r.2)
  have hpow : ∀ (j : ℕ) (x : A), (σ ^ j) x = τ^[j] x := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, Function.iterate_succ_apply']
      rfl
  have hpowF : ∀ (j : ℕ) (z : F₁), τ^[j] (algebraMap F₁ A z) = algebraMap F₁ A ((sb ^ j) z) := by
    intro j z
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hτ, pow_succ', AlgEquiv.mul_apply]
  have hGal : UpperTheory.ConvolutionTheory.D.IsGal σ (Module.finrank F₀ F₁) := by
    refine ⟨hG.pos, AlgEquiv.ext fun x => ?_, Subtype.val_injective, fun r hr => ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    · rw [hpow, hd]; rfl
    · obtain ⟨s, x, y, h⟩ := hG.sep
      refine ⟨s, fun i => algebraMap F₁ A (x i), fun i => algebraMap F₁ A (y i), fun j hj => ?_⟩
      simp only [hpow, hpowF, ← map_mul, ← map_sum]
      rw [h j hj]
      split_ifs <;> simp
  have hu : IsUnit c := by
    have h1 : c ∣ UpperTheory.Gal.InertialTypesAlt.L.itN τ (Module.finrank F₀ F₁) c :=
      Finset.dvd_prod_of_mem (fun i => τ^[i] c) (Finset.mem_range.2 hG.pos)
    rw [hc] at h1
    exact isUnit_of_dvd_one h1
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 F₀ F₀ S A σ _ hGal hu.unit (by
    simp only [hpow, IsUnit.unit_spec]
    exact hc)
  exact ⟨z, hz⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTrace
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin mapGL)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

private theorem exists_trace {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (m : Measure (GL (Fin n) k)) [m.IsHaarMeasure]
    (τ : SmIrr (GL (Fin n) k)) (φ : GL (Fin n) k → ℂ) (hφ : Test φ) : ∃ z, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace m τ.ρ φ z := by
  obtain ⟨l1, -, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of k n
  have hA := (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff τ.ρ).1 (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred)
  obtain ⟨A, hA1, hA2⟩ := PositivityTheory.TfC.OccursIff.exists_integralOp_of_admissible m τ.ρ hA φ hφ.1 hφ.2
  exact ⟨_, A, hA1, hA2, rfl⟩

private theorem fin_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (U : Subgroup (GL (Fin n) k)) (ho : IsOpen (U : Set (GL (Fin n) k)))
    (hc : IsCompact (U : Set (GL (Fin n) k))) : FiniteDimensional ℂ (fixed τ.ρ U) :=
  (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred).2 U ho hc

private theorem twKer_keep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (θ : G → G) (hθ : ∀ u ∈ U, θ u ∈ U) (I : V →ₗ[ℂ] V) (hI : ∀ g x, I (ρ g x) = ρ (θ g) (I x)) :
    ∀ x ∈ twKer ρ U 1, I x ∈ twKer ρ U 1 := by
  have h : twKer ρ U 1 ≤ (twKer ρ U 1).comap I := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    refine Submodule.subset_span ⟨⟨θ u, hθ u u.2⟩, I x, ?_⟩
    simp [hI]
  exact fun x hx => h hx

private theorem cmp_onto {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) (g : Gw n w.1) :
    ∃ y : GL (Fin n) (CompletionsOver E v), GM.cmp w y = g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let e := RingEquiv.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)
  refine ⟨mapGL n (e.symm : _ →+* _) g, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact e.apply_symm_apply (g i j)

end UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

open UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

theorem UpperTheory.Gal.InertialTypesAlt.L.inflTrace :
    GlobalTheory.DZA.InflMatching → UpperTheory.Gal.InertialTypesAlt.G.VarEx → UpperTheory.Gal.InertialTypesAlt.G.VarTrace → UpperTheory.Gal.InertialTypesAlt.G.NormInt → UpperTheory.Gal.InertialTypesAlt.L.InflTrace := by
  intro hIM hVE hVT hNI F E _ _ _ _ _ _ _ _ hp n hn π P hconj hweak v w hw hunr _ _ _ _ hcm F₀ F₁ _ _ _ _ _ rk rK s sb hres τ τ' hτ hτ'
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨hgen, hfr⟩ := UpperTheory.Gal.InertialTypesAlt.L.frobFacts _ _ F₀ F₁ rk rK s sb hres
  obtain ⟨hns, hdeg, hglob⟩ := UpperTheory.Gal.InertialTypesAlt.L.globOf F E hp v w hw hcm
  obtain ⟨σ, hσg, hσs⟩ := hglob s hgen
  obtain ⟨s', hs', hI⟩ := hVE F E σ hσg hp n hn P hconj v w hns
  obtain ⟨I₀, hI₀⟩ := hI τ' hτ'

  have hsg : ∀ g : Gw n w.1, s' g = GlobalTheory.LBC.galAct s n g := by
    intro g
    obtain ⟨y, rfl⟩ := cmp_onto w hw g
    have e := hs' y
    change (s' : Gw n w.1 →* Gw n w.1) (GM.cmp w y) = _
    rw [← e]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hσs (y i j)

  obtain ⟨a, ha, hTw⟩ := UpperTheory.Gal.InertialTypesAlt.L.twScale _ _ s hgen n τ'.V τ'.ρ τ'.smooth τ'.irred I₀
    (fun g x => by rw [hI₀, hsg])
  let I₂ : τ'.V ≃ₗ[ℂ] τ'.V := I₀.trans (LinearEquiv.smulOfNeZero ℂ τ'.V a ha)
  have hI₂c : (I₂ : τ'.V →ₗ[ℂ] τ'.V) = a • (I₀ : τ'.V →ₗ[ℂ] τ'.V) := rfl
  have hI₂ : ∀ g x, I₂ (τ'.ρ g x) = τ'.ρ (s' g) (I₂ x) := fun g x => by
    change a • I₀ (τ'.ρ g x) = τ'.ρ (s' g) (a • I₀ x)
    rw [hI₀, map_smul]

  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hP⟩ := @UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E _ _ _ _ _ _ σ hσg v w hw _ _ _ _ s hgen hdeg hcm hσs n _ _ _ _ mE mF hE hF _ _
  have hUS := UpperTheory.V.Z.Tf.Orb.unitSB_holds
  have hPI := UpperTheory.V.Z.Tf.Orb.placeInt_holds
  have hcmp : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hE1 : (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)))
      (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.1.adicCompletion E) : Set (GL (Fin n) (w.1.adicCompletion E))) = 1 := by
    rw [Measure.map_apply hcmp.measurable (hUS _ n).1.measurableSet, ← hPI.2 F E v w hw n, h1]
  have hF1 : mF (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) = 1 := by
    rw [hPI.1 F v n, h2]
  obtain ⟨c, hc, hcT⟩ := hVT F E σ hσg hp n hn π P hconj hweak v w hns mF _ hF hH τ τ' hτ hτ' (s' : Gw n w.1 →* Gw n w.1) I₂ hs' hI₂
  refine ⟨(I₂ : τ'.V →ₗ[ℂ] τ'.V), c, by rw [hI₂c]; exact hTw, hc, fun fb hfb => ?_⟩
  obtain ⟨hKk, hUko, hUkc, hUkle, -, hfk⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₀ rk hres.onto₀ n
  obtain ⟨hKK, hUKo, hUKc, hUKle, -, hfK⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₁ rK hres.onto₁ n
  obtain ⟨hHk, hTk, hSk⟩ := hfk fb
  obtain ⟨hHK, hTK, -⟩ := hfK (normLift sb fb)
  obtain ⟨hst1, -, -⟩ := hfr n
  have hstab : ∀ u ∈ K1 rK n, GlobalTheory.LBC.galAct s n u ∈ K1 rK n := fun u hu => by
    have : GlobalTheory.LBC.galAct s n u ∈ (K1 rK n).map (GlobalTheory.LBC.galAct s n) := Subgroup.mem_map_of_mem _ hu
    rwa [hst1] at this
  obtain ⟨hm1, hm2⟩ := hIM _ _ (UpperTheory.V.Z.Tf.Orb.extCont_of _ _).1 inferInstance F₀ F₁ hres.deg rk rK hres.onto₀ hres.onto₁
    hres.inc s sb hres.gal hres.frob n fb hfb
  rw [hKk, hKK] at hm1
  rw [hKk] at hm2
  have hM := UpperTheory.Gal.InertialTypesAlt.L.matchOfSum _ _ s hgen n _ mF hH hF hE1 hF1 (K1 rK n) (K1 rk n) _ _
    ⟨hUKo, hKK ▸ hUKle, hstab⟩ ⟨hUko, hKk ▸ hUkle, fun _ h => h⟩ hHK hHk hm1 hm2
  have hMA : GM.MatchAt σ v 1 (fun g => infl rK (normLift sb fb) (GM.cmp w g)) (infl rk fb) :=
    @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ (hP _ hTK _ hTk hM)
  have hsupp : ∀ g, infl rk fb g ≠ 0 → g ∈ UpperTheory.Gal.InertialTypesAlt.G.normSet E n v := fun g hg =>
    hNI F E σ hσg hp n hn v hunr g (by
      have h3 : g ∈ (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) := by
        have := hSk g hg
        rwa [hKk] at this
      rw [hPI.1 F v n] at h3
      exact h3)
  obtain ⟨z, hz⟩ := exists_trace mF τ _ hTk
  obtain ⟨B, hB, hBt⟩ := hcT _ _ 1 z hTK hTk hMA hsupp hz
  obtain ⟨A, hA, hAt⟩ := hz
  obtain ⟨l1, s1, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (v.adicCompletion F) n
  obtain ⟨l2, s2, t2, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (w.1.adicCompletion E) n
  have e1 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hH (KO _ n) (by rw [hKK]; exact (hUS _ n).1) (by rw [hKK]; exact (hUS _ n).2.1)
    (by rw [hKK]; exact hE1) _ τ'.ρ τ'.smooth (K1 rK n) hUKo hUKle _ hHK (I₂ : τ'.V →ₗ[ℂ] τ'.V)
    (fun x hx => by rw [hI₂c]; exact hTw.mem_fixed hst1 hx)
    (twKer_keep _ _ (GlobalTheory.LBC.galAct s n) hstab _ (fun g x => (hI₂ g x).trans (congrArg (fun h => τ'.ρ h (I₂ x)) (hsg g))))
    B _ hB hBt (fin_fixed τ' _ hUKo hUKc)
  have e2 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hF (KO _ n) (by rw [hKk]; exact (hUS _ n).1) (by rw [hKk]; exact (hUS _ n).2.1)
    (by rw [hKk]; exact hF1) _ τ.ρ τ.smooth (K1 rk n) hUko hUkle _ hHk LinearMap.id (fun _ h => h) (fun _ h => h)
    A z hA hAt (fin_fixed τ _ hUko hUkc)
  rw [← e1, ← e2, mul_one]
end

