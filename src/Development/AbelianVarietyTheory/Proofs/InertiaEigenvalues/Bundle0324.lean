import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

noncomputable section

open Pointwise

namespace GlobalTheory.SelInf

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_Ine {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

variable {R R' : Type} [CommRing R] [CommRing R'] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  {S : Set (HeightOneSpectrum (𝓞 F))} {ρ : Representation R (G F Ω) M} {ρS : Representation R' (GS Ω S) M'}
  (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρS (toGS Ω S g) (e m))

include he in

theorem triv_of_mem {σ : G F Ω} (hσ : σ ∈ NS Ω S) (m : M) : ρ σ m = m := by
  apply e.injective
  have : toGS Ω S σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
  rw [he, this, map_one]
  rfl

def infZ (z : Z1 ρS) : Z1 ρ :=
  ⟨fun g => e.symm (z.1 (toGS Ω S g)),
    (continuous_of_discreteTopology (f := e.symm)).comp (z.2.1.comp (continuous_toGS Ω S)), fun g h => by
      apply e.injective
      beta_reduce
      rw [map_add, he, map_mul, z.2.2]
      simp⟩

theorem infZ_apply (z : Z1 ρS) (g : G F Ω) : (infZ e he z).1 g = e.symm (z.1 (toGS Ω S g)) := rfl

theorem mk_infZ_eq_iff (z z' : Z1 ρS) :
    (Submodule.Quotient.mk (infZ e he z) : H1 ρ) = Submodule.Quotient.mk (infZ e he z') ↔
      (Submodule.Quotient.mk z : H1 ρS) = Submodule.Quotient.mk z' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun g => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    have h1 : e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = ρ g m - m := hm g
    have h2 := congrArg e h1
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, fun g => ?_⟩
    have h1 : z.1 (toGS Ω S g) - z'.1 (toGS Ω S g) = ρS (toGS Ω S g) m - m := hm (toGS Ω S g)
    change e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = _
    apply e.injective
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact h1

def infH : H1 ρS → H1 ρ := fun x => Submodule.Quotient.mk (infZ e he x.out)

theorem infH_mk (z : Z1 ρS) : infH e he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (infZ e he z) :=
  (mk_infZ_eq_iff e he _ _).2 (Quotient.out_eq' _)

theorem infH_injective : Function.Injective (infH e he) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [infH_mk, infH_mk] at h
  exact (mk_infZ_eq_iff e he _ _).1 h

theorem Ine_le_NS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

theorem z_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] {π : Representation R Γ M} (z : Z1 π) : z.1 1 = 0 := by
  have := z.2.2 1 1
  simpa using this

include he in

theorem mem_unrAt_iff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (z : Z1 ρ) :
    resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  have h0 : resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val
        (restrictCocycles1 ρ (Dec (F := F) A).subtype continuous_subtype_val z)) : H1 _) = 0 := Iff.rfl
  rw [h0, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h1 : z.1 σ = ρ σ m - m := hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩
    rw [h1, triv_of_mem e he (Ine_le_NS hv hA hσ), sub_self]
  · intro h
    refine ⟨0, fun g => ?_⟩
    rw [map_zero, sub_zero]
    exact h g.1.1 g.2

include he in

theorem vanish_NS [IsAlgClosure F Ω] (A : Formalism.GaloisCohomology.Places F Ω) (z : Z1 ρ)
    (h : ∀ v ∉ S, ∀ σ ∈ Ine (F := F) (A.1 v), z.1 σ = 0) : ∀ σ ∈ NS Ω S, z.1 σ = 0 := by
  have hz := z.2.2
  have hinv : ∀ g, z.1 g + ρ g (z.1 g⁻¹) = 0 := fun g => by
    rw [← hz, mul_inv_cancel, z_one]
  let K : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ z.1 g = 0}
      one_mem' := ⟨one_mem _, z_one z⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [hz, ha', hb', map_zero, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have := hinv a
        rwa [ha', zero_add, triv_of_mem e he ha] at this }
  have hK : K.Normal := ⟨by
    rintro a ⟨ha, ha'⟩ g
    refine ⟨(normal_NS S).conj_mem a ha g, ?_⟩
    rw [mul_assoc, hz, hz, ha', zero_add, triv_of_mem e he ha, hinv]⟩
  have hc : IsClosed (K : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter ((isClosed_discrete {(0 : M)}).preimage z.2.1)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A) ≤ K := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hB
    have h1 := conj_Ine (F := F) hτ
    have h2 : g⁻¹ * τ * g ∈ K := ⟨Ine_le_NS hv (A.2 v) h1, h v hv _ h1⟩
    have h3 := hK.conj_mem _ h2 g
    have h4 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rwa [h4] at h3
  intro σ hσ
  exact (Subgroup.topologicalClosure_minimal _ hle hc hσ).2

theorem exists_infZ (z : Z1 ρ) (h : ∀ σ ∈ NS Ω S, z.1 σ = 0) : ∃ z', infZ e he z' = z := by
  have hz := z.2.2
  have hw : ∀ a b : G F Ω, (QuotientGroup.leftRel (NS Ω S)) a b → e (z.1 a) = e (z.1 b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have : z.1 (a * (a⁻¹ * b)) = z.1 a := by rw [hz, h _ hab, map_zero, add_zero]
    rw [← this, mul_inv_cancel_left]
  refine ⟨⟨Quotient.lift (fun g => e (z.1 g)) hw,
    Continuous.quotient_lift ((continuous_of_discreteTopology (f := e)).comp z.2.1) hw, fun g g' => ?_⟩, ?_⟩
  · obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    obtain ⟨g', rfl⟩ : ∃ g'', toGS Ω S g'' = g' := QuotientGroup.mk'_surjective _ g'
    rw [← map_mul]
    change e (z.1 (g * g')) = e (z.1 g) + ρS (toGS Ω S g) (e (z.1 g'))
    rw [hz, map_add, he]
  · exact Subtype.ext (funext fun g => e.symm_apply_apply (z.1 g))

end

theorem selAll_equiv_sel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R R' : Type) [CommRing R] [CommRing R'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M'] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω) (ρ : Representation R (G F Ω) M) (ρS : Representation R' (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M') (e : M ≃+ M'), ContAction ρ → (∀ g m, e (ρ g m) = ρS (toGS Ω _ g) (e m)) → ∀ (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (LS : LocCond ρS (locFam S (fun v => A.1 v.1))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ (v : S) (z : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)) (z' : Z1 (ρS.comp (locFam S (fun v => A.1 v.1) v))), (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L v.1 ↔ Submodule.Quotient.mk z' ∈ LS v)) → Nonempty (Formalism.GaloisCohomology.SelAll ρ A L ≃ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS) := by
  intro F Ω _ _ _ _ _ R R' _ _ M _ _ _ _ M' _ _ _ _ S A ρ ρS e _ he L LS hL hLS
  have key : ∀ (z : Z1 ρS) (v : S),
      resH1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (Submodule.Quotient.mk (infZ e he z)) ∈ L v.1 ↔
      resH1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) (Submodule.Quotient.mk z) ∈ LS v :=
    fun z v => hLS v (restrictCocycles1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e he z))
      (restrictCocycles1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g => (e.apply_symm_apply _).symm)
  have hall : ∀ y : H1 ρ, y ∈ Formalism.GaloisCohomology.SelAll ρ A L ↔
      ∀ v, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val y ∈ L v :=
    fun y => mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L y
  have hmem : ∀ x : H1 ρS, x ∈ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS ↔
      infH e he x ∈ Formalism.GaloisCohomology.SelAll ρ A L := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk, hall, mem_Sel]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · exact (key z ⟨v, hv⟩).2 (h ⟨v, hv⟩)
      · rw [hL v hv, mem_unrAt_iff e he (by simpa using hv) (A.2 v)]
        intro σ hσ
        have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
          (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
        rw [infZ_apply, this, z_one, map_zero]
    · intro h v
      exact (key z v).1 (h v.1)
  refine ⟨(Equiv.ofBijective (fun x : Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS =>
    (⟨infH e he x.1, (hmem _).1 x.2⟩ : Formalism.GaloisCohomology.SelAll ρ A L)) ⟨?_, ?_⟩).symm⟩
  · intro x y h
    exact Subtype.ext (infH_injective e he (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' := (hall _).1 hy
    obtain ⟨z', rfl⟩ := exists_infZ e he z (vanish_NS e he A z fun v hv => by
      have hv' : v ∉ S := by simpa using hv
      have := hy' v
      rwa [hL v hv', mem_unrAt_iff e he hv (A.2 v)] at this)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem _).2 (by rw [infH_mk]; exact hy)⟩, Subtype.ext (infH_mk e he z')⟩

end GlobalTheory.SelInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResSel.CoefMap

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →ₛₗ[σ] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def semilinearCoefficientMapCocycles : Z1 rho →ₛₗ[σ] Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add, he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' c z := Subtype.ext (funext fun g => map_smulₛₗ u _ _)

def slH1 : H1 rho →ₛₗ[σ] H1 rho' :=
  Submodule.mapQ _ _ (semilinearCoefficientMapCocycles rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem res_slH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (slH1 rho rho' u hu he x) =
      slH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem slH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    slH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_slH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₐ[O] K') (r : ℕ)

def vecMap : (Fin r → K) →ₛₗ[(f : K →+* K')] (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_smul' c m := funext fun a => map_mul f _ _

theorem vecMap_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecMap f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecMap f r m) := by
  funext a
  simp [vecMap, repOn, matAct, map_sum]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')

theorem slH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    slH1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecMap f r) continuous_of_discreteTopology (fun g m => vecMap_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (vecMap f r) continuous_of_discreteTopology
        (fun g m => vecMap_repOn f ρ g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, smul_eq_mul, map_mul, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem slH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) :
    slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
      (vecMap_repOn f ρ) x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
    (vecMap_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact slH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem cl_mem_selOn_of_algHom (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (K K' : Type)
    [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    [Field K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')
    (Q : Finset (PlE D.host)) (x : Z1 (red i K ρ)) (x' : Z1 (red i K' ρ)) (h : ∀ g a, x'.1 g a = f (x.1 g a))
    (hx : cl x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : cl x' ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  have e : x' = semilinearCoefficientMapCocycles _ _ (vecMap f D.R.r) continuous_of_discreteTopology (vecMap_repOn f ρ) x :=
    Subtype.ext (funext fun g => funext fun a => h g a)
  rw [e]
  exact slH1_mem_selOn bkP i ρ f Q (cl x) hx

end GlobalTheory.ResSel.CoefMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableLinearFormOnConstants
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNe
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosureStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_invariant_approx_by_epsilonRoots_closure : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  first | exact @GlobalTheory.FlatInvariants.flat_invariant_approx | exact GlobalTheory.FlatInvariants.flat_invariant_approx | (intros; apply GlobalTheory.FlatInvariants.flat_invariant_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧ (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧ (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧ (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  first | exact @GlobalTheory.PSer.Laws.sh_laws | exact GlobalTheory.PSer.Laws.sh_laws | (intros; apply GlobalTheory.PSer.Laws.sh_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandardStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPhiGammaModel_character_eq_standard : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  first | exact @GlobalTheory.Models.CharModel.model_chr_eq | exact GlobalTheory.Models.CharModel.model_chr_eq | (intros; apply GlobalTheory.Models.CharModel.model_chr_eq <;> assumption)
end

