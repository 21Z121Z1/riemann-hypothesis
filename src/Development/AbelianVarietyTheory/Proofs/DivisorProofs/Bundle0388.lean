import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem smul_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    {b : K} (hb : b ∈ B) {y : DR k K} (hy : y ∈ omB k K B q) : b • y ∈ omB k K B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨b * c, B.mul_mem hb hc, v, hv, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul r y _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h

theorem ιMulti_D_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    (w : Fin q → B) : (ExteriorAlgebra.ιMulti K q fun j => D k K (w j : K)) ∈ omB k K B q := by
  apply Submodule.subset_span
  exact ⟨1, B.one_mem, fun j => (w j : K), fun j => (w j).2, (one_smul K _).symm⟩

theorem omB_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K,
    Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧
    ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  intro k K _ _ _ B _ _ q
  haveI : Algebra.FormallyEtale B K := .of_isLocalization (nonZeroDivisors B)
  let φ : Ω[B⁄k] →ₗ[B] Ω[K⁄k] := KaehlerDifferential.map k k B K
  have hD : ∀ x : B, φ (D k B x) = D k K (x : K) := fun x => KaehlerDifferential.map_D k k B K x
  have hφ : IsBaseChange K φ := IsBaseChange.of_equiv (tensorKaehlerEquivOfFormallyEtale k B K) fun x => by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl
  let E := GlobalTheory.exteriorPowerMapOver K q φ
  have hE : IsLocalizedModule (nonZeroDivisors B) E :=
    (isLocalizedModule_iff_isBaseChange _ K E).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ q)
  haveI : Module.Projective B (⋀[B]^q Ω[B⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective B Ω[B⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination B id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat B (⋀[B]^q Ω[B⁄k]) := inferInstance
  haveI : Module.IsTorsionFree B (⋀[B]^q Ω[B⁄k]) := Module.Flat.isTorsionFree
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors B) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[B]^q Ω[B⁄k])
      (isRegular_of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  let e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K := ((⋀[K]^q Ω[K⁄k]).subtype.restrictScalars B) ∘ₗ E
  have hι : ∀ a : Fin q → Ω[B⁄k], e (exteriorPower.ιMulti B q a) =
      ExteriorAlgebra.ιMulti K q fun j => φ (a j) := by
    intro a
    change ((E (exteriorPower.ιMulti B q a) : ⋀[K]^q Ω[K⁄k]) : DR k K) = _
    rw [GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.ιMulti_apply_coe]
  have hιD : ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
    intro v
    rw [hι]
    simp only [hD]
  have hB : ∀ (b : B) (y : DR k K), b • y = (b : K) • y := fun b y => (algebraMap_smul K b y).symm
  refine ⟨e, Subtype.val_injective.comp hEinj, fun y => ⟨fun hy => ?_, ?_⟩, hιD⟩
  · have : omB k K B q ≤ LinearMap.range (e.restrictScalars k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      refine ⟨(⟨b, hb⟩ : B) • exteriorPower.ιMulti B q (fun j => D k B ⟨v j, hv j⟩), ?_⟩
      rw [LinearMap.restrictScalars_apply, map_smul, hιD, hB]
    obtain ⟨z, hz⟩ := this hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span B q Ω[B⁄k] (span_range_derivation k B)
    have hz : z ∈ Submodule.span B
        (⇑(exteriorPower.ιMulti B q) '' {a | Set.range a ⊆ Set.range (D k B)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k B (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [hιD]
      exact ιMulti_D_mem_omB_regForms B q w
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul b z _ h => rw [map_smul, hB]; exact smul_mem_omB_regForms B q b.2 h

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanX
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC

theorem ker_reduceLoc_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  intro T O _ _ _ _ _ _ A A₁ _ _ f i i₁ EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit hker
  have hψ : ∀ p : A₁[X], algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) p =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) p) :=
    fun _ => rfl
  have hC : ∀ c : A₁, algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) c =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) (C c)) := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), IsScalarTower.algebraMap_apply A₁ A₁[X] (Ext f EA)]
    rfl
  have hlocX : locBC f i i₁ EA QA jA hcomp hj (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA), locBC_algebraMap]
    have h1 : inclE f EA (algebraMap A[X] EA Polynomial.X) =
        algebraMap A[X] (Ext f EA) Polynomial.X :=
      (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
    rw [h1, Algebra.TensorProduct.algebraMap_apply, algebraMap_polyOver, Polynomial.map_X]
    rfl
  have hpol : ∀ q : A₁[X],
      Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X})
        (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) q)) =
      Ideal.Quotient.mk _ (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (Polynomial.eval 0 q)) := by
    intro q
    rw [hC, Ideal.Quotient.eq, ← map_sub, ← map_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [hr, map_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : (Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X}) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* _) =
      (Ideal.Quotient.mk _).comp ((algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x =>
      rw [reduce_tmul]
      dsimp only
      have hsplit : (p ⊗ₜ[A[X]] x : Ext f EA) =
          algebraMap A₁[X] (Ext f EA) p * inclE f EA x := by
        show (p ⊗ₜ[A[X]] x : Ext f EA) = (p ⊗ₜ[A[X]] (1 : EA)) * ((1 : PolyOver f) ⊗ₜ[A[X]] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      simp only [map_mul]
      congr 1
      · exact hpol p
      · rw [← locBC_algebraMap, ← locBC_algebraMap_base]
        have hmem : algebraMap EA (Localization.AtPrime QA) x -
            algebraMap A (Localization.AtPrime QA) (ρ (algebraMap EA (Localization.AtPrime QA) x)) ∈
              RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub]
          have := congrArg (fun w => w (ρ (algebraMap EA (Localization.AtPrime QA) x))) hρA
          simp only [RingHom.comp_apply, RingHom.id_apply] at this
          rw [this, sub_self]
        rw [hker, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, hlocX]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simp only [map_add, hx, hy]
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h := congrArg (fun w => w x) key
    simp only [RingHom.comp_apply, hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X) = 0
    rw [hψ, reduceLoc, IsLocalization.lift_eq,
      show algebraMap A₁[X] (Ext f EA) Polynomial.X = (@id (PolyOver f) Polynomial.X) ⊗ₜ[A[X]] (1 : EA)
        from rfl, reduce_tmul]
    show Polynomial.eval 0 (Polynomial.X : A₁[X]) * _ = 0
    rw [Polynomial.eval_X, zero_mul]

end GlobalTheory.KeyOriginBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFg
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  first | exact @GlobalTheory.EtC.kumCoker_bijective | exact GlobalTheory.EtC.kumCoker_bijective | (intros; apply GlobalTheory.EtC.kumCoker_bijective; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

namespace GlobalTheory.EtC.GmStep

variable (R : Type) [CommRing R]

def rowD (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) :
    H R (disc.obj (E.obj (op ⦋p⦌))) F s →+ H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s

def RowExact (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) : Prop :=
  ∀ y : H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s, rowD R E F s (p + 1) y = 0 → ∃ z, rowD R E F s p z = y

variable {R}

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
private theorem map_rowDifferential_of_commute_faces_lemma {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s) :
    φ (p + 1) (_root_.GlobalTheory.EtC.GmStep.rowD R E F s p y) =
      _root_.GlobalTheory.EtC.GmStep.rowD R E' F' s' p (φ p y) := by
  simp only [_root_.GlobalTheory.EtC.GmStep.rowD, AddMonoidHom.finset_sum_apply,
    AddMonoidHom.smul_apply, map_sum, map_zsmul, hc]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.rowExact_transfer {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hφ : ∀ p, Function.Bijective (φ p))
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (h : _root_.GlobalTheory.EtC.GmStep.RowExact R E F s p) : _root_.GlobalTheory.EtC.GmStep.RowExact R E' F' s' p := by
  intro y' hy'
  obtain ⟨y, rfl⟩ := (hφ (p + 1)).2 y'
  have hy : _root_.GlobalTheory.EtC.GmStep.rowD R E F s (p + 1) y = 0 := by
    apply (hφ (p + 1 + 1)).1
    rw [map_rowDifferential_of_commute_faces_lemma φ hc, hy', map_zero]
  obtain ⟨z, rfl⟩ := h y hy
  exact ⟨φ p z, (map_rowDifferential_of_commute_faces_lemma φ hc p z).symm⟩

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f) (laurentVarUnit B)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  simp [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_C]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℤ) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  have hu : ((_root_.GlobalTheory.EtC.laurentVarUnit B : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  have hinv : (((_root_.GlobalTheory.EtC.laurentVarUnit B)⁻¹ : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T (-1) := by
    rw [← Units.inv_mul_cancel_left (_root_.GlobalTheory.EtC.laurentVarUnit B)
      (LaurentPolynomial.T (-1)), hu, ← LaurentPolynomial.T_add]
    simp
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_T]
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, hu, ← LaurentPolynomial.T_add]
  · rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C =
      (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f :=
  RingHom.ext fun a => _root_.GlobalTheory.EtC.GmStep.laurentMap_C f a

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f p).coeff = Finsupp.mapRange f f.map_zero p.coeff := by
  refine LaurentPolynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq,
      Finsupp.mapRange_add (map_add f)]
  · rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.mapRange_single]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_isIntegral {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) : (_root_.GlobalTheory.EtC.GmStep.laurentMap f).IsIntegral := by
  letI := (_root_.GlobalTheory.EtC.GmStep.laurentMap f).toAlgebra
  intro x
  change IsIntegral (LaurentPolynomial A) x
  refine LaurentPolynomial.induction_on' x (fun p q hp hq => hp.add hq) (fun n b => ?_)
  refine IsIntegral.mul ?_ ?_
  · obtain ⟨P, hm, hP⟩ := hf b
    refine ⟨P.map LaurentPolynomial.C, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C)
      (LaurentPolynomial.C b) P = 0
    rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C, ← Polynomial.hom_eval₂, hP, map_zero]
  · rw [← _root_.GlobalTheory.EtC.GmStep.laurentMap_T f n]
    exact isIntegral_algebraMap

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_ker {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    RingHom.ker (_root_.GlobalTheory.EtC.GmStep.laurentMap f) ≤ nilradical (LaurentPolynomial A) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hc : ∀ n, f (x.coeff n) = 0 := by
    intro n
    have h := congrArg (fun g => g n) (_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff f x)
    rw [hx] at h
    simpa using h.symm
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T]
  refine Ideal.mul_mem_right _ _ ?_
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk (RingHom.mem_ker.mpr (hc n)))).map _)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.spec_integral_surj {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hi : φ.IsIntegral) (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ⟨?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  intro P
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B)
    (fun a ha => nilradical_le_prime P.asIdeal
      (hk (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)))))
  refine ⟨⟨Q, hQ⟩, ?_⟩
  change PrimeSpectrum.comap φ ⟨Q, hQ⟩ = P
  exact PrimeSpectrum.ext hQP

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev baseHom : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev laurentHom : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constSq : Arrow.mk (yoneda.map (laurentHom A A')) ⟶ Arrow.mk (yoneda.map (baseHom A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentMap_comp_C])

def cechC : cech (laurentHom A A') ⟶ cech (baseHom A A') := Arrow.mapCechNerve (constSq A A')

def augK (k : ℕ) : disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌)) ⟶ sch.obj (Spec (CommRingCat.of (LaurentPolynomial A))) :=
  disc.map ((cechAug (laurentHom A A')).app (op ⦋k⦌))

def rowOne (q : ℕ) (i : ℤ) (k : ℕ) :
    Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) 0 (i - 1) →+ Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) 1 i where
  toFun a := (cup q (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a)
    (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A)))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add, AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC.GmStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfEtalePuncturedStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_algHom_of_etale_punctured : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] (φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B)), ∃ ψ : A →ₐ[R] B, (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R B))).comp ψ = φ := by
  first | exact @GlobalTheory.LiftHom.liftHom_of_etale_punctured | exact GlobalTheory.LiftHom.liftHom_of_etale_punctured | (intros; apply GlobalTheory.LiftHom.liftHom_of_etale_punctured <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearMapFibreRankSplitCompSurjectiveStatement
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapFibreRank_split_comp_surjective : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  first | exact @GlobalTheory.FibreRanks.fibre_ranks | exact GlobalTheory.FibreRanks.fibre_ranks | (intros; apply GlobalTheory.FibreRanks.fibre_ranks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
end

