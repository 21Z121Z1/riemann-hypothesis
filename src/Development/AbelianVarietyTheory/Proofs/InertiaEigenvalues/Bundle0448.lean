import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointObjectsTransportAlongConjugationOverFractio
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
section
noncomputable section
namespace GlobalTheory.TopSteps.CharBound
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

theorem exists_ext {k G : Type} [Field k] [Group G] (A : Ob k G) (z : G → Fin A.m → k)
    (h1 : z 1 = 0) (hz : ∀ g h, z (g * h) = z g + A.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin A.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt A E z ∧
      ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := by
  let π : Representation k G ((Fin A.m → k) × k) :=
    { toFun := fun g => ((A.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [h1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨m, y⟩ := x
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := fun g x y => he g (x, y)
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simp at this
    exact this.symm
  · simpa using he' g x 0
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := e.injective hx
    simp at this
  · rw [← he']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add]
    simp

theorem exists_resEquiv {O k : Type} [CommRing O] [Field k] [Algebra O k] {c : O}
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x) :
    ∃ e : (O ⧸ Ideal.span {c}) ≃ₗ[O] k, ∀ y, e (Ideal.Quotient.mk _ y) = algebraMap O k y := by
  have h : Ideal.span {c} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [Ideal.mem_span_singleton, LinearMap.mem_ker, Algebra.linearMap_apply, hk]
  exact ⟨(Submodule.quotEquivOfEq _ _ h).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs),
    fun _ => rfl⟩

section
variable {O G k : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field k] [Algebra O k]

theorem exists_ext_Ea {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) (χ : G →* Oˣ)
    {X : Type} [AddCommGroup X] [Module O X] {c : O} (hc : ∀ x : X, c • x = 0)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) (A : Ob k G) (q : (M ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W χ X g x) = A.ρ g (q x)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] (Fin E.m → k)),
      IsExt A E (fun g => q ((z : G → M ⊗[O] X) g)) ∧
      ∀ σ x, e (twistRep (Ea W χ hc z) χ⁻¹ σ x) = E.ρ σ (e x) := by
  obtain ⟨r, hr⟩ := exists_resEquiv hs hk
  obtain ⟨E, e, hE, he⟩ := exists_ext A (fun g => q ((z : G → M ⊗[O] X) g)) (by simp [cocycle_one])
    (fun g h => by rw [cocycle_mul z g h, map_add, hq])
  refine ⟨E, (q.prodCongr r).trans (e.restrictScalars O), hE, ?_⟩
  rintro σ ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have : twistRep (Ea W χ hc z) χ⁻¹ σ (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X σ m + y • (z : G → M ⊗[O] X) σ, Ideal.Quotient.mk _ y) := by
    rw [Ea, twistRep_apply, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [this]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.restrictScalars_apply, map_add,
    map_smul, hq, hr]
  rw [← he, algebraMap_smul]

theorem linearIndependent_of_indepMod {N : Type} [AddCommGroup N] [Module O N] (π : Representation O G N)
    {lam : O} (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    (A : Ob k G) (q : N ≃ₗ[O] (Fin A.m → k)) (hq : ∀ g x, q (π g x) = A.ρ g (q x)) {s : ℕ}
    (z : Fin s → ↥(Z1 π ⊤)) (h : IndepMod lam (fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤))) :
    LinearIndependent k (fun a => (cob A).mkQ (fun g => q ((z a : G → N) g))) := by
  rw [Fintype.linearIndependent_iff]
  intro y hy a
  choose x hx using fun a => hs (y a)
  rw [← hx, hk]
  refine h x ?_ a
  simp only [← map_smul, ← map_sum] at hy
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  have e1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.mkQ _ (∑ a, x a • z a) := by
    rw [map_sum]; rfl
  rw [e1]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨q.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply q.injective
  have := congrFun hb g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply,
    ← hx, algebraMap_smul] at this
  change q (π g (q.symm b) - q.symm b) = _
  rw [map_sub, hq, q.apply_symm_apply, this]
  simp
end

theorem exists_charEquiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O k : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [Field k] [Algebra O k]
    (Γ : GalData G Qp LL O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (ω : G →* kˣ) (hω : ∀ σ, (ω σ : k) = algebraMap O k (Γ.ε σ))
    (c : ℕ) :
    ∃ q : (O ⊗[O] GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) ≃ₗ[O] (Fin (chr (ω ^ (-((c : ℤ) - 1)))).m → k),
      ∀ g x, q (twCoef (Γ.Wchi c) Γ.χ₁ _ g x) = (chr (ω ^ (-((c : ℤ) - 1)))).ρ g (q x) := by
  obtain ⟨r, -⟩ := exists_resEquiv hs hk
  refine ⟨((TensorProduct.lid O _).trans r).trans (LinearEquiv.funUnique (Fin 1) O k).symm, fun g x => ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, map_smul]
  have h : ω g = Units.map (algebraMap O k : O →* k) (Γ.ε g) := Units.ext (hω g)
  have h2 : (((ω ^ (-((c : ℤ) - 1))) g : kˣ) : k) = algebraMap O k ((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) := by
    rw [MonoidHom.zpow_apply, h, ← map_zpow]; rfl
  have h3 : ∀ (θ : G →* kˣ) (v : Fin 1 → k), (chr θ).ρ g v = (θ g : k) • v := fun _ _ => rfl
  rw [h3, h2, algebraMap_smul]

section
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O) {k : Type} [Field k] [Algebra O k]

theorem lam_smul_resK (x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) : Γ.lam ^ 1 • x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem exists_cocycles_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} {R : RingPG k l} {F : DFun R n G} (M : ModTh F D)
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    {V : Type} [AddCommGroup V] [Module O V] (W : Representation O G V) {X : Type} [AddCommGroup X] [Module O X]
    (hX : ∀ x : X, Γ.lam ^ 1 • x = 0) (A : Ob k G) (q : (V ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W Γ.χ₁ X g x) = A.ρ g (q x))
    {s : ℕ} (x : Fin s → H1 (twCoef W Γ.χ₁ X) ⊤)
    (hx : ∀ a, x a ∈ admAt PD emb Γ D.t D.Ut W X 1 hX) (hi : IndepMod Γ.lam x) :
    ∃ z : Fin s → G → Fin A.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles A) ∧
      LinearIndependent k (fun a => (cob A).mkQ (z a)) := by
  choose z hz hadm using hx
  obtain rfl : x = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨fun a g => q ((z a : G → V ⊗[O] X) g), fun a => ?_,
    linearIndependent_of_indepMod _ hs hk A q hq z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea W Γ.χ₁ hX hs (fun y => by rw [pow_one]; exact hk y) (z a) A q hq
  obtain ⟨L, hL⟩ := hM E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem bound_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}
    {F : DFun R n G} (M : ModTh F D) (h1 : D.T1 l) (h2 : D.T2 l) (h3 : D.T3 l)
    (hω : ∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ))
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (hfin : Finite (O ⧸ Ideal.span {Γ.lam})) (c : ℕ)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut (Γ.Wchi c) X = admAt PD emb Γ D.t D.Ut (Γ.Wchi c) X a ha)
    (s : ℕ) (x : Fin s → H1 (twCoef (Γ.Wchi c) Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hx : ∀ a, x a ∈ adm PD emb Γ D.t D.Ut (Γ.Wchi c) (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ))
    (hi : IndepMod Γ.lam x) : (2 ≤ c → c ≤ D.t → s ≤ 0) ∧ (c = 1 → s ≤ 1) := by
  rw [h0 _ 1 (lam_smul_resK Γ) le_rfl] at hx
  obtain ⟨q, hq⟩ := exists_charEquiv Γ hs hk M.ω hω c
  have key := exists_cocycles_gen PD emb D Γ hs hk M hM (Γ.Wchi c) (lam_smul_resK Γ) _ q hq x hx hi
  clear hq q hx hi x hM
  refine ⟨fun hc hct => ?_, fun hc => ?_⟩
  · obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    let a : Fin s := ⟨0, by omega⟩
    exact hli.ne_zero a ((Submodule.Quotient.mk_eq_zero _).mpr
      (GlobalTheory.T.admissibleCocycles_neg_char_pow_mem_cob F M h1 h2 h3 ((c : ℤ) - 1) (by omega) (by omega) (z a) (hz a)))
  · have e : M.ω ^ (-((c : ℤ) - 1)) = 1 := by simp [hc]
    rw [e] at key
    obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    have h2s : 2 ≤ s := by omega
    exact GlobalTheory.T.trivialLine_admissibleCocycles_not_independent F M h1 h2 h3 (fun a => z (Fin.castLE h2s a)) (fun a => hz _)
      (hli.comp _ (Fin.castLE_injective h2s))

end

theorem exists_res {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ} [Fact l.Prime]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ 1})) {lam : O}
    (hlam : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k) (_ : CharP k l),
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer lam).mp hlam
  have hl' : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hl
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective,
    fun x => ?_⟩
  · refine Finite.of_surjective _ (Ideal.Quotient.factor_surjective (S := Ideal.span {((l : ℕ) : O) ^ 1}) ?_)
    rw [pow_one, ← hm, Ideal.span_singleton_le_iff_mem]
    exact hl'
  · rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl'
  · rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem resBound_chars : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Real →
    (∀ c : ℕ, 2 ≤ c → c ≤ S.D.t → S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0) ∧
    (S.Lem0 (S.Γ.Wchi 1) → S.ResBound (S.Γ.Wchi 1) 1) := by
  intro l _ P S hR
  obtain ⟨hSt, -, h1, h2, h3⟩ := S.hyp
  obtain ⟨hd, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete S.LL
  obtain ⟨hfin, k, _, _, _, hs, hk⟩ := exists_res hl ((GlobalTheory.LocalIntegers.good_integers l S.LL).2 1)
    hSt.2.2.2.2.2
  obtain ⟨R, ι, -, F, M, hω, -, hM⟩ := hR k ⟨hs, hk⟩
  have key := bound_gen (P.PD S.K) S.emb S.D S.Γ hs hk M h1 h2 h3 hω hM hfin
  refine ⟨fun c hc hct h0 s x hx hi => ?_, fun h0 s x hx hi => ?_⟩
  · have key' := key c (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).1 hc hct
  · have key' := key 1 (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).2 rfl

end GlobalTheory.TopSteps.CharBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReduction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKTorsionRed

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {ρ : Representation LL G V}

theorem coboundary_mem_blochKato_cocycles (m : V) (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

def latticeCoboundaryCocycle (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) : ↥(latticeCocycles L) :=
  ⟨fun g => ρ g x - x, Submodule.mem_inf.2 ⟨(coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)).1,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩⟩

theorem lattice_reduction_coboundary_mem_cocycles (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (x : ↥L.T) :
    redT L I (latticeCoboundaryCocycle PD L hρ x) = LinearMap.pi (fun g => actQ L I hI g - LinearMap.id) (I.mkQ x) := by
  funext g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mkQ_apply, actQ,
    Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rfl

theorem mem_HfQ_iff (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ a : ↥(latticeCocycles L), (a : G → V) ∈ finiteCocycles PD ρ ∧ c = redT L I a := by
  constructor
  · intro h
    obtain ⟨_, ⟨a0, ha0, rfl⟩, _, ⟨xb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨a0 + latticeCoboundaryCocycle PD L hρ x, (finiteCocycles PD ρ).add_mem ha0.2 (coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)), ?_⟩
    rw [map_add, lattice_reduction_coboundary_mem_cocycles PD L hρ I hI x]
    rfl
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.mem_sup_left ⟨a, ⟨a.2, ha⟩, rfl⟩

theorem mem_HfQ_iff_red : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  intro l _ P K LL _ _ _ O _ _ _hO A LA ϖ r hI c
  exact mem_HfQ_iff (P.PD K) LA A.cont _ hI c

end GlobalTheory.BKTorsionRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRayPrincipalIdealsInfOfUnitsPmOne
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RayPrincipalInf

open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals

variable {K : Type} [Field K] [NumberField K]

theorem not_mem_of_coprime {𝔞 𝔭 : Ideal (𝓞 K)} {b : 𝓞 K} (h : IsCoprime (Ideal.span {b}) 𝔞) (hle : 𝔞 ≤ 𝔭)
    (hp : 𝔭 ≠ ⊤) : b ∉ 𝔭 := by
  intro hb
  apply hp
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hb) hle

end GlobalTheory.RayPrincipalInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemZpowersOfTameGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TameCycChoice

theorem zpow_iff {Γ L A F : Type} [Group Γ] [Field L] [CommRing A] [Field F] (e : L →+* F) (j : A →+* F)
    (hj : Function.Injective j) (ψ₀ : Γ →* Lˣ) (ψ : Γ →* Aˣ)
    (h : ∀ g, e ((ψ₀ g : Lˣ) : L) = j ((ψ g : Aˣ) : A)) (σ γ : Γ) (m : ℤ) :
    ψ σ = ψ γ ^ m ↔ ψ₀ σ = ψ₀ γ ^ m := by
  rw [← map_zpow, ← map_zpow, ← Units.val_inj, ← Units.val_inj, ← hj.eq_iff, ← e.injective.eq_iff, h, h]

theorem mem_zpowers_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (B : ValuationSubring Ω) {Γ : Type} [Group Γ] (ψ : G E Ω →* Γ) (ho : IsOpen (ψ.ker : Set (G E Ω)))
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → ψ σ = 1)
    {γ : G E Ω} (hγ : TameGenAt B γ) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) B) :
    ψ σ ∈ Subgroup.zpowers (ψ γ) := by
  let K : Subgroup (G E Ω) := (Subgroup.zpowers (ψ γ)).comap ψ
  have hK : IsOpen (K : Set (G E Ω)) := Subgroup.isOpen_mono (H₁ := ψ.ker)
    (fun g hg => by rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hg]; exact one_mem _) ho
  refine closure_minimal (t := (K : Set (G E Ω))) ?_ (K.isClosed_of_isOpen hK) (hγ.2 hσ)
  refine (Subgroup.closure_le K).2 ?_
  rintro g (rfl | hg)
  · exact Subgroup.mem_zpowers _
  · change ψ g ∈ Subgroup.zpowers _
    rw [hw g hg]; exact one_mem _

theorem tameCyc : ∀ (D : D7) (C : NChoice D), NChTie D C → TameCyc D C := by
  intro D C hT i v hv σ hσ
  obtain ⟨ψ₀, -, hW, hK⟩ := hT.psi_eq
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hmem := mem_zpowers_of_tameGen (D.nd.plOm.1 v) (D.ntw.psiL i) (D.ntw.psiL_open i)
    (fun g hg => GlobalTheory.WildInertiaChar.trivial_on_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i)
      (D.nd.lPrime i).out hl (D.nd.plOm.2 v) _ (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) g hg)
    (D.nd.restN_tameGenerator_generates i v (Or.inr hv)) σ hσ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨m, ?_⟩
  have h0 := (zpow_iff (D.nd.embK i) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
    (IsFractionRing.injective _ _) (ψ₀ (D.nd.w i)) (D.ntw.psiL i) (hK i) σ (D.nd.gam0 i v) m).1 hm.symm
  exact (zpow_iff (C.embW (D.nd.w i))
    ((algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))))
    ((IsFractionRing.injective (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp (C.Oe_inj (D.nd.w i)))
    (ψ₀ (D.nd.w i)) (psiG D C (D.nd.w i)) (hW (D.nd.w i)) σ (D.nd.gam0 i v) m).2 h0

end GlobalTheory.TameCycChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibniz
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_choose_succ_nsmul (fun i j => (fun τ => (⇑(derivative K))^[i] (f τ)) • (C.nabla ^ j) v) k,
      pow_succ', Module.End.mul_apply, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', Module.End.mul_apply]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimesStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_at_type_primes : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.NoLocalInvariants.noInv_of_adm2At | exact GlobalTheory.NoLocalInvariants.noInv_of_adm2At | (intros; apply GlobalTheory.NoLocalInvariants.noInv_of_adm2At <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFixAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.UnramInertia

theorem norm_sub_lt_one_of_fix : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l), (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) →
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  intro l _ σ hσ x hx
  have hmem : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 hσ
  exact GlobalTheory.FrobGen.norm_sub_lt hmem x hx

end GlobalTheory.UnramInertia
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLeStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  first | exact @GlobalTheory.untilt_ext_sum_sub_le | exact GlobalTheory.untilt_ext_sum_sub_le | (intros; apply GlobalTheory.untilt_ext_sum_sub_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_powerSeries_of_null_ainf_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S), (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) → ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  first | exact @GlobalTheory.NullOverS.null_of_mul_null | exact GlobalTheory.NullOverS.null_of_mul_null | (intros; apply GlobalTheory.NullOverS.null_of_mul_null <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointGaloisReps_conjugate_over_fraction_field : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  first | exact @GlobalTheory.PointRepConj.main | exact GlobalTheory.PointRepConj.main | (intros; apply GlobalTheory.PointRepConj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointObjectsTransportAlongConjugationOverFractioStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointObjects_transport_along_conjugation_over_fraction_field : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), (∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)))) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) → ∀ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S → ∃ S' : IdempotentChoiceData N i, S'.g0 = S.g0 ∧ GoodCongruenceObjects N r' ρ' π S' := by
  first | exact @GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | exact GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | (intros; apply GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupReal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
end

