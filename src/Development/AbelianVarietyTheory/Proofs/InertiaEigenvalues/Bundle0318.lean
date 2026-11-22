import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.GWComplex

section Count

variable {R : Type*} [CommRing R] {A B C D E : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]

theorem card_eq_ker_mul_range (f : A →ₗ[R] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

theorem card_five {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {k : D →ₗ[R] E}
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h)
    (h3 : Function.Exact h k) :
    Nat.card (LinearMap.ker k) * Nat.card B = Nat.card C * Nat.card A := by
  rw [card_eq_ker_mul_range g, card_eq_ker_mul_range h, h1.linearMap_ker_eq,
    h2.linearMap_ker_eq, h3.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]
  ring

theorem card_comap {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (L : Submodule R B) :
    Nat.card (L.comap f) =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker (g.domRestrict L)) := by
  let u : L.comap f →ₗ[R] L := f.restrict (fun _ hx => hx)
  rw [card_eq_ker_mul_range u]
  have e1 : LinearMap.range u = LinearMap.ker (g.domRestrict L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, h x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact x.2⟩, Subtype.ext hy⟩
  have e2 : Nat.card (LinearMap.ker u) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.1 x.2]; exact L.zero_mem⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2]

theorem card_pi {I : Type*} [Fintype I] {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (L : ∀ i, Submodule R (P i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i trivial⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Count

theorem arith {k p h2 h0 s i h1 s' q h0' m : ℕ} (a1 : k * p = h2 * h0) (a2 : s = k * i)
    (a3 : i * h1 = s' * q) (a4 : h0' * h2 * m = h1) : s * h0' * p * m = s' * h0 * q := by
  calc s * h0' * p * m = (k * p) * i * h0' * m := by rw [a2]; ring
    _ = i * (h0' * h2 * m) * h0 := by rw [a1]; ring
    _ = s' * h0 * q := by rw [a4, a3]; ring

open PoitouTate in

theorem ker_flip_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Av : S → ValuationSubring Ω}
    {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
    {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
    (hj : ∀ v, Function.Injective (j v))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}
    (hρ : ContAction ρ) (L : LocCond ρ (locFam S Av)) :
    LinearMap.ker ((tr1 S Av μ j ρ hρ).domRestrict (Submodule.pi Set.univ L)).flip =
      Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)
        (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) := by
  classical
  ext y
  rw [mem_Sel, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [mem_perpCond, LinearMap.flip_apply, LinearMap.domRestrict_apply, poitouTateNineTerm_transgressionOne_apply,
    LinearMap.zero_apply]
  constructor
  · intro h v x hx
    have hm : Pi.single v x ∈ Submodule.pi Set.univ L := fun w _ => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
    have e := h ⟨_, hm⟩
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [Subtype.coe_mk, Pi.single_eq_of_ne hw, map_zero, map_zero]) (by simp),
      Subtype.coe_mk, Pi.single_eq_same] at e
    exact hj v (e.trans (map_zero _).symm)
  · intro h x
    exact Finset.sum_eq_zero fun v _ => by rw [h v _ (x.2 v trivial), map_zero]

open PoitouTate in

theorem greenbergWiles_totallyComplex : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (S : Finset (HeightOneSpectrum (𝓞 F))) (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), 0 < r → ContainsAbove S l → ∀ (hrho : ContAction rhoS) (muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ), muS.comp (toGS Ω _) = cycMod F Ω l r → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond rhoS (locFam S Av), Finite (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) ∧ Finite (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) ∧ Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) * Nat.card (H0 (twDual muS rhoS)) * (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) * Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hS hρ μ hμ Av hA L
  classical
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨inv, hinv, h⟩ := hPT F Ω l r hr ζ hζ
  obtain ⟨⟨δ₁, -, h0, h1, h2, h3, h4, -⟩, -⟩ := h S hS Av hA μ hμ M ρ hρ
  have := GlobalTheory.DualSide.finite_TDual_pow (l := l) (r := r) (M := M)
  have hρ' := GlobalTheory.DualSide.contAction_twDual (contAction_charRep hμ) hρ
  obtain ⟨-, f1, -⟩ := hGF F Ω l r M S ρ hr hS hρ
  obtain ⟨-, f1', f2', -⟩ := hGF F Ω l r _ S (twDual μ ρ) hr hS hρ'
  have fl : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v =>
    (hLF F Ω l r M (Av v) _ v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have a1 := card_five h0 h1 h2 h3
  rw [GlobalTheory.ZModDual.card_dual_eq, Nat.card_pi] at a1
  have a2 := card_comap h4 (Submodule.pi Set.univ L)
  have e2 : (Submodule.pi Set.univ L).comap (loc1 S Av ρ) =
      Sel ρ (locFam S Av) (continuous_locFam S Av) L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [e2] at a2
  have a3 := GlobalTheory.ZModDual.card_ker_mul_card_eq (l ^ r) _ _
    ((tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ).domRestrict (Submodule.pi Set.univ L))
  rw [ker_flip_eq (fun v => (invAt_bijective S Av μ hμ hinv v (hA v)).1), card_pi] at a3
  have a4 := hEC F Ω l r _ S (twDual μ ρ) hr hS hρ' (fun _ => 1)
    (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)))
  have hM : Nat.card (TDual (ZMod (l ^ r)) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq _ _
  rw [archH0Card, Finset.filter_false_of_mem (fun w _ =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)), Finset.prod_empty,
    one_mul, hM, IsTotallyComplex.finrank, two_mul, pow_add, ← mul_assoc] at a4
  have a5 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) a4
  exact arith a1 a2 a3 a5

end GlobalTheory.GWComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocCommStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ), IsClass α → IsClass β → IsClass γ → (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧ (n = a + b → hc a b α β n = hc b a β α n) ∧ (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) := by
  first | exact @GlobalTheory.GLq.HcRing.main | exact GlobalTheory.GLq.HcRing.main | (intros; apply GlobalTheory.GLq.HcRing.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def permGL {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) : GL α K :=
  ⟨π.symm.toPEquiv.toMatrix, π.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem glEquiv_perm {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) (g : GL α K) :
    glEquiv K π g = permGL π * g * (permGL π)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.reindex π π (g : Matrix α α K) =
    π.symm.toPEquiv.toMatrix * (g : Matrix α α K) * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def repIsoOf {G : Type} [Group G] (V W : FDRep ℂ G) (L : (V : Type) ≃ₗ[ℂ] (W : Type))
    (h : ∀ g v, L (V.ρ g v) = W.ρ g (L v)) : V ≅ W :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso L) (fun g => by
    ext v
    exact h g v)

def rhoEquiv {G : Type} [Group G] (σ : FDRep ℂ G) (P : G) : (σ : Type) ≃ₗ[ℂ] (σ : Type) :=
  LinearEquiv.ofLinear (σ.ρ P) (σ.ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (σ.ρ P * σ.ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (σ.ρ P⁻¹ * σ.ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_conj {G : Type} [Group G] (σ : FDRep ℂ G) (P X : G) (w : (σ : Type)) :
    σ.ρ P (σ.ρ X w) = σ.ρ (P * X * P⁻¹) (σ.ρ P w) := by
  rw [show σ.ρ (P * X * P⁻¹) (σ.ρ P w) = σ.ρ (P * X * P⁻¹ * P) w by rw [map_mul σ.ρ (P * X * P⁻¹) P]; rfl,
    inv_mul_cancel_right, map_mul]
  rfl

theorem lab_transp_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (σ : FDRep ℂ (GL α K)) (e : α ≃ β) (d : ℕ) (e₁ : α ≃ Fin d) (e₂ : β ≃ Fin d) :
    O.lab d (transp e₁ σ) = O.lab d (transp e₂ (transp e σ)) := by
  apply O.lab_iso
  let π : α ≃ α := e₁.trans (e.trans e₂).symm
  have hA : ∀ γ : GL (Fin d) K, (glEquiv K e).symm ((glEquiv K e₂).symm γ) =
      glEquiv K π ((glEquiv K e₁).symm γ) := by
    intro γ
    apply Units.ext
    ext i j
    simp [π, Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv]
  refine ⟨repIsoOf _ _ (rhoEquiv σ (permGL π)) fun γ v => ?_⟩
  show σ.ρ (permGL π) (σ.ρ ((glEquiv K e₁).symm γ) v) =
    σ.ρ ((glEquiv K e).symm ((glEquiv K e₂).symm γ)) (σ.ρ (permGL π) v)
  rw [hA, glEquiv_perm]
  exact rho_conj σ _ _ v

theorem labO_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : FDRep ℂ (GL α K)) :
    labO O (transp e σ) = labO O σ := by
  have key : ∀ (d : ℕ) (e₂ : β ≃ Fin d) (d' : ℕ) (e₁ : α ≃ Fin d'),
      O.lab d (transp e₂ (transp e σ)) = O.lab d' (transp e₁ σ) := by
    intro d e₂ d' e₁
    have hd : d = d' := by
      have h1 := Fintype.card_congr e₂
      have h2 := Fintype.card_congr e₁
      have h3 := Fintype.card_congr e
      simp only [Fintype.card_fin] at h1 h2
      omega
    subst hd
    exact (lab_transp_transp O σ e d e₁ e₂).symm
  exact key _ _ _ _

end GlobalTheory.SerOSys.TranspLabel

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end GlobalTheory.SerOSys.TranspLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenspaceSumDisjointCompl
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_disjoint_compl : ∀ (D : D7) (i : D.nd.Loc) (Y : Set (D.nd.X i)),
    Disjoint (D.nd.eigSum i Y) (D.nd.eigSum i Yᶜ) := by
  intro D i Y
  exact (Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right

end GlobalTheory.EtaJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModuleStatement
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondFormStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_restriction_polynomial_condition_second_form : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  first | exact @GlobalTheory.Cut.PolynomialInertiaAction.main | exact GlobalTheory.Cut.PolynomialInertiaAction.main | (intros; apply GlobalTheory.Cut.PolynomialInertiaAction.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDuality
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem int_iso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : ReciprocityTheory.ChartRestriction.T2.IntIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinv x hx
  haveI := hD.t2'
  haveI : IsGalois K (PadicAlgCl p) := inferInstance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  induction x using Submodule.Quotient.induction_on with
  | H c => ?_
  by_contra hx0
  have hcB : (c : G → VT ⧸ D.T) ∉ B1 D.ρA := fun h => hx0 ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨r, hr⟩ := GlobalTheory.T.continuous_quotient_torsion_bounded D.T hD.lat hD.openT ϖ hϖ (c : G → VT ⧸ D.T) c.2.1
  have hcyc : ∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧
      ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := by
    intro g n ζ hζ
    obtain ⟨a, h1, h2⟩ := hD.cyc (i g) n ζ hζ
    have e : (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) (i g) = D.ε g := by
      change D.ε (i.symm (i g)) = D.ε g
      exact congrArg D.ε (i.symm_apply_apply g)
    rw [e] at h2
    exact ⟨a, h1, h2⟩
  obtain ⟨hcpt, hopen, hbasis⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hO.compact hF.emb hD.lat hD.perf hD.t2' ϖ hϖ
  haveI := hcpt
  let X : ℕ → Type := fun k => G → ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)
  let Y : ∀ k, Set (X k) := fun k => {z | z ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) ∧
    cupMod D (c : G → VT ⧸ D.T) ϖ (r + k) z ∉ B2 (twist D.ε (KO O))}
  have hle : ∀ k, r + k ≤ r + (k + 1) := fun k => by omega
  let f : ∀ k, X (k + 1) → X k := fun k z g =>
    Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)
  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i D.ρTl' (sub_contAction D.contT' _ D.stT') ϖ hϖ hopen (r + k)).subset
      (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := fun k => by
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel hT hK hO.ring hO.compact hO.t2 hO.adic hO.p_mem hO.p_ne hF.emb i D
      hcyc hD.lat hD.perf hD.contT hD.openT hD.t2 hD.t2' hD.cs hD.cs' ϖ hϖ c.1 c.2 hcB r hr (r + k)
      (by omega)
    exact ⟨z, hz, hz'⟩
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_cocycles_pow_quot D.ρTl' ϖ (hle k) hz, ?_⟩
    have e := cupMod_factor D hr (Nat.le_add_right r k) (hle k) z
    show cupMod D (c : G → VT ⧸ D.T) ϖ (r + k)
      (fun g => Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)) ∉ _
    rw [e]
    exact hnc
  obtain ⟨s, hs⟩ := GlobalTheory.exists_compatible_seq_of_finite_nonempty X f Y hfin hne hmap
  let w : ℕ → G → ↥D.T' := fun k g => qlift (s k g)
  have hwZ : ∀ k, (fun g => (Submodule.Quotient.mk (w k g) :
      ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) := by
    intro k
    have e : (fun g => (Submodule.Quotient.mk (w k g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) =
        s k := funext fun g => mk_qlift _
    rw [e]
    exact (hs k).1.1
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ powSub (M := ↥D.T') ϖ (r + k) := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    have e1 : (Submodule.Quotient.mk (w (k + 1) g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)) =
        f k (s (k + 1)) g := by
      show _ = Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (s (k + 1) g)
      conv_rhs => rw [← mk_qlift (s (k + 1) g)]
      rfl
    rw [e1, (hs k).2]
    exact (mk_qlift (s k g)).symm
  obtain ⟨e, he, hew⟩ := GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' D.ρTl' ϖ r hopen hbasis w hwZ hstep
  have h1 := hx (Submodule.Quotient.mk ⟨e, he⟩)
  have h2 : ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) ∈ B2 (twist D.ε (KO O)) := by
    have h3 : D.inv (Submodule.Quotient.mk (cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩)) = D.inv 0 := by
      rw [map_zero]
      exact h1
    have h6 := (Submodule.Quotient.mk_eq_zero _).1 (hinv h3)
    exact h6
  apply (hs 0).1.2
  have h4 : cupMod D (c : G → VT ⧸ D.T) ϖ (r + 0) (s 0) = ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) := by
    funext q
    refine pairKO_eq_of_sub_mem D (hr q.1) ?_
    rw [← map_sub]
    refine powSub_stable _ ϖ r q.1 _ ?_
    have h5 := hew 0 q.2
    rw [← neg_sub]
    exact Submodule.neg_mem _ h5
  rw [h4]
  exact h2

end GlobalTheory.LocDualInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2TopStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_H2_top : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admH2 i := by
  first | exact @GlobalTheory.IntTateTop.admH2_of_duality | exact GlobalTheory.IntTateTop.admH2_of_duality | (intros; apply GlobalTheory.IntTateTop.admH2_of_duality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDualStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_pairing_lattice_dual : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T), (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧ (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  first | exact @GlobalTheory.TatePair.integral_pairing | exact GlobalTheory.TatePair.integral_pairing | (intros; apply GlobalTheory.TatePair.integral_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isDR_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  intro l _ P n _ _ K V _ _ b ρ Q hQ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK
  haveI : Nontrivial P.R.BdR := by
    refine ⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] P.R.BdR V n b
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x :=
    fun g x => P.PD_actdR K g x
  have key := GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K)
    (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR))
    (fun x => ⟨fun h => (P.PD K).invdR x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actdR g).commutes c⟩) Q
    (fun g => by
      have h := hQ g
      have : (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l) :=
        funext (hact g)
      rw [this]
      exact h)
    ((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔
          y ∈ DdR (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y
      have h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b] at key
  exact key

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
end

