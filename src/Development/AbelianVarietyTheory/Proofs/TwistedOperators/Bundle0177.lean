import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankOneProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)]

omit [Fintype α] [LinearOrder α] [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in

theorem isEmpty_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) : IsEmpty (c a) :=
  ⟨fun x => ha (congrArg Sigma.fst (g.injective (Subsingleton.elim (g ⟨a, x⟩) (g (g.symm ())))))⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in

theorem det_eq_one_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) (x : GL (c a) k) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have := isEmpty_of_ne g ha
  ext
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α]
  [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in

theorem mem_parab_unit (g : (Σ i, c i) ≃ Unit) (x : GL Unit k) : x ∈ parab k g :=
  mem_parab.2 fun _ _ h => absurd h (lt_irrefl _)

theorem deltaHalf_eq_one (g : (Σ i, c i) ≃ Unit) (x : Levi k c) : deltaHalf k c x = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = (g.symm ()).1
  · have h : modExp c a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne)
        simp
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne')
        simp
    simp [h]
  · rw [det_eq_one_of_ne g ha, map_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem piTensor_leviProj (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ) (p : parab k g)
    (w : PiTensorProduct ℂ fun _ : α => ℂ) :
    piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p) w =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) • w := by
  have hd : (∏ a, (detChar (c a) (ψ a) (leviProj k g p a) : ℂ)) =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) := by
    rw [Finset.prod_eq_single (g.symm ()).1, detChar_apply, detChar_apply, det_parab,
      Finset.prod_eq_single (g.symm ()).1]
    · intro b _ hb
      exact det_eq_one_of_ne g hb _
    · simp
    · intro b _ hb
      rw [detChar_apply, det_eq_one_of_ne g hb, map_one, Units.val_one]
    · simp
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod, smul_comm, ← hd, ← MultilinearMap.map_smul_univ]
    congr 2

theorem nonempty_equiv_multiProd_unit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type)
    [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) :
    Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  let L : (PiTensorProduct ℂ fun _ : α => ℂ) ≃ₗ[ℂ] ℂ :=
    (PiTensorProduct.constantBaseRingEquiv α ℂ).toLinearEquiv
  have law : ∀ (φ : IndSp g (piTensor fun i => detRep (c i) (ψ i))) (x : GL Unit k),
      φ.1.1 x = (detChar Unit (ψ (g.symm ()).1) x : ℂ) • φ.1.1 1 := fun φ x => by
    have := parInd_law g _ φ ⟨x, mem_parab_unit g x⟩ 1
    rw [deltaHalf_eq_one g, piTensor_leviProj, mul_one, Units.val_one, one_smul] at this
    exact this
  let f : IndSp g (piTensor fun i => detRep (c i) (ψ i)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => L (φ.1.1 1)
      map_add' := fun φ φ' => map_add L _ _
      map_smul' := fun r φ => map_smul L r _ }
  refine ⟨LocGL.equivOfBijective ⟨f, fun x => LinearMap.ext fun φ => ?_⟩ ⟨fun φ φ' h => ?_, fun z => ?_⟩⟩
  · show L (φ.1.1 (1 * x)) = detRep Unit (ψ (g.symm ()).1) x (L (φ.1.1 1))
    rw [one_mul, law, map_smul]
    exact (ofChar_apply _ _ _).symm
  · have h1 : φ.1.1 1 = φ'.1.1 1 := L.injective h
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [law φ x, law φ' x, h1]
  · refine ⟨⟨⟨fun x => (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z, fun p x => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds ((hψ (g.symm ()).1).detChar (n := Unit)) (one_mem _)) fun y hy => ?_)⟩, ?_⟩
    · show (detChar Unit (ψ (g.symm ()).1) (p * x) : ℂ) • L.symm z =
        (deltaHalf k c (leviProj k g p) : ℂ) • piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p)
          ((detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z)
      rw [deltaHalf_eq_one g, piTensor_leviProj, Units.val_one, one_smul, map_mul, Units.val_mul,
        mul_smul]
    · have hy' : detChar Unit (ψ (g.symm ()).1) y = 1 := hy
      apply Subtype.ext
      funext x
      show (detChar Unit (ψ (g.symm ()).1) (x * y) : ℂ) • L.symm z =
        (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z
      rw [map_mul, hy', mul_one]
    · show L ((detChar Unit (ψ (g.symm ()).1) 1 : ℂ) • L.symm z) = z
      rw [map_one, Units.val_one, one_smul, L.apply_symm_apply]

end GlobalTheory.SmGL.RankOneProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.Exponents

section Bool

variable {X : Bool → Type} [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)]

def boolPair (v : X false) (w : X true) : ∀ x, X x
  | false => v
  | true => w

def boolMulti : MultilinearMap ℂ X (X false ⊗[ℂ] X true) :=
  MultilinearMap.mk' (fun x => x false ⊗ₜ[ℂ] x true)
    (fun m i x y => by cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add])
    (fun m i c x => by cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])

theorem boolPair_eq_right (v : X false) (w w' : X true) :
    boolPair v w = Function.update (boolPair v w') true w := by
  funext x; cases x <;> simp [boolPair]

theorem boolPair_eq_left (v v' : X false) (w : X true) :
    boolPair v w = Function.update (boolPair v' w) false v := by
  funext x; cases x <;> simp [boolPair]

def boolBilin : X false →ₗ[ℂ] X true →ₗ[ℂ] PiTensorProduct ℂ X :=
  LinearMap.mk₂ ℂ (fun v w => PiTensorProduct.tprod ℂ (boolPair v w))
    (fun v v' w => by
      rw [boolPair_eq_left (v + v') 0, boolPair_eq_left v 0, boolPair_eq_left v' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_left (c • v) 0, boolPair_eq_left v 0, MultilinearMap.map_update_smul])
    (fun v w w' => by
      rw [boolPair_eq_right v (w + w') 0, boolPair_eq_right v w 0, boolPair_eq_right v w' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_right v (c • w) 0, boolPair_eq_right v w 0, MultilinearMap.map_update_smul])

def boolTensorEquiv : PiTensorProduct ℂ X ≃ₗ[ℂ] X false ⊗[ℂ] X true :=
  LinearEquiv.ofLinear (PiTensorProduct.lift boolMulti) (TensorProduct.lift boolBilin)
    (by
      ext v w
      simp [boolBilin, boolMulti, boolPair])
    (by
      ext x
      simp only [boolBilin, boolMulti, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply, TensorProduct.lift.tmul,
        LinearMap.mk₂_apply, LinearMap.id_apply]
      congr 1
      funext i
      cases i <;> rfl)

theorem boolTensorEquiv_tprod (x : ∀ i, X i) :
    boolTensorEquiv (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true := by
  simp [boolTensorEquiv, boolMulti]

end Bool

def piTensorTwoEquiv {R a b V W : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    (piTensor (twoRep π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo R a b).symm.toMonoidHom) :=
  .mk (boolTensorEquiv (X := Two V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show boolTensorEquiv (X := Two V W) (piTensor (twoRep π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo R a b).symm g) (boolTensorEquiv (X := Two V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, boolTensorEquiv_tprod, boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo R a b).symm g) (x false) (x true)).symm

theorem prod₂_equiv_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type)
    [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) :=
  ⟨(LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv π₁ π₂)).symm⟩

end GlobalTheory.SmGL.Exponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
section
noncomputable section

namespace GlobalTheory.LFun.SplitVal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

private lemma sigR_tmul_adelic_iwasawa_hecke {K L : Type} [Field K] [Field L] [Algebra K L] {τ : L →ₐ[K] L} {R : Type} [CommRing R]
    [Algebra K R] (r : R) (e : L) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R τ (r ⊗ₜ[K] e) = r ⊗ₜ[K] τ e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]

private lemma extZero_tmul {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] (a : Af K) (e : L) :
    extZero K L (a ⊗ₜ[K] e) = (LinearMap.inr K (Ainf K) (Af K) a : AF K) ⊗ₜ[K] e :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a e

omit [NumberField E] in
theorem sigR_extZero (y : Af F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (extZero F E y) = extZero F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [sigR_tmul_adelic_iwasawa_hecke, extZero_tmul, extZero_tmul]
    exact sigR_tmul_adelic_iwasawa_hecke (R := AF F) (LinearMap.inr F (Ainf F) (Af F) a) e
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem evalV_sigR (y : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma map_evalV_eq_of_finAdEquiv_eq {v' : HeightOneSpectrum (𝓞 F)} {y₁ y₂ : Af F ⊗[F] E}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v' → finAdEquiv F E y₁ u = finAdEquiv F E y₂ u) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₁ =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₂ := by
  have hev1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 1 := by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v' = 1
    exact RestrictedProduct.single_eq_same _ _ _
  have hev0 : ∀ v'' : HeightOneSpectrum (𝓞 F), v'' ≠ v' →
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v'' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 0 :=
    fun v'' hv => by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v'' = 0
    exact RestrictedProduct.single_eq_of_ne _ _ hv
  have hs1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) = 1 := by
    rw [Algebra.TensorProduct.map_tmul, hev1, AlgHom.id_apply]; rfl
  have key : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₁ =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₂ := by
    apply (finAdEquiv F E).injective
    refine FiniteAdeleRing.ext _ fun u => ?_
    rw [map_mul, map_mul]
    change finAdEquiv F E _ u * finAdEquiv F E y₁ u = finAdEquiv F E _ u * finAdEquiv F E y₂ u
    by_cases hu : u.under (𝓞 F) = v'
    · rw [H u hu]
    · rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), Algebra.TensorProduct.map_tmul, hev0 _ hu,
        TensorProduct.zero_tmul, map_zero, zero_mul, zero_mul]
  have := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)) key
  rwa [map_mul, map_mul, hs1, one_mul, one_mul] at this

theorem single_apply_ne (x : (w.adicCompletion E)ˣ) {u : HeightOneSpectrum (𝓞 E)} (hu : u ≠ w) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) u = 1 := by
  classical
  first
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) u = 1
     exact RestrictedProduct.mulSingle_eq_of_ne _ _ hu)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     simp [Pi.mulSingle, Function.update, hu])

private lemma cmval_single_apply_self (x : (w.adicCompletion E)ˣ) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) w = x := by
  classical
  first
  | (change (Pi.mulSingle w (x : w.adicCompletion E) : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) w = x
     exact Pi.mulSingle_eq_same _ _)
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) w = x
     exact RestrictedProduct.mulSingle_eq_same _ _)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     exact Pi.mulSingle_eq_same _ _)

theorem sigR_single (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ ((finAdEquiv F E).symm
      (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)) =
    (finAdEquiv F E).symm (GlobalTheory.CMVal.single w' (Units.map (complMap h').toMonoidHom a) : FiniteAdeleRing (𝓞 E) E) := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne h h'
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) h' h
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have hz1 : GlobalTheory.AdelicU.splitProj τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = (a : Fv F v) := by
    apply (complMap h).injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← finAdEquiv_apply h, RingEquiv.apply_symm_apply, cmval_single_apply_self]
    rfl
  have hz2 : GlobalTheory.AdelicU.splitProj (τ.comp σ) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = 1 := by
    apply (complMap h').injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', ← finAdEquiv_apply h', RingEquiv.apply_symm_apply, map_one]
    exact single_apply_ne _ (Ne.symm hne)
  apply (finAdEquiv F E).injective
  rw [RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  by_cases hu : u.under (𝓞 F) = v
  · have hu2 : u = w ∨ u = w' := by
      by_cases huw : u = w
      · exact Or.inl huw
      · right
        obtain ⟨τu, hτu, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE huw hu h
        rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τu with e | e
        · exact absurd (hτu.symm.trans (e ▸ hτ)) huw
        · rw [← hτu, e, hτ']
    rcases hu2 with huw | huw
    · rw [huw, finAdEquiv_apply h, evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← GlobalTheory.AdelicU.splitProj_comp,
        hz2, map_one]
      exact (single_apply_ne _ hne).symm
    · rw [huw, finAdEquiv_apply h', evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ',
        GlobalTheory.AdelicU.splitProj_comp_sigR hE τ, hz1, cmval_single_apply_self]
      rfl
  · have h1 := map_evalV_eq_of_finAdEquiv_eq (v' := u.under (𝓞 F))
      (y₁ := (finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E))
      (y₂ := 1) (fun u' hu' => by
        rw [RingEquiv.apply_symm_apply, map_one]
        exact single_apply_ne _ (by rintro rfl; exact hu (hu'.symm.trans h)))
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), evalV_sigR, h1]
    simp only [map_one]
    exact (single_apply_ne _ (by rintro rfl; exact hu h')).symm

private lemma coe_locIdele' (u : HeightOneSpectrum (𝓞 E)) (x : (u.adicCompletion E)ˣ) :
    ((locIdele F u x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single u x : FiniteAdeleRing (𝓞 E) E)) := rfl

theorem sigR_locIdele (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (locIdele F w (Units.map (complMap h).toMonoidHom a) : AF F ⊗[F] E) =
      locIdele F w' (Units.map (complMap h').toMonoidHom a) := by
  rw [coe_locIdele', coe_locIdele', map_add, map_sub, map_one, sigR_extZero, sigR_extZero, map_one,
    sigR_single hE h h' hne a]

theorem val_mul_val_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  intro F E _ _ _ _ _ σ hE μ b hμ w w' hww hne hw hw'
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne rfl hww.symm
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) hww.symm rfl
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have ha := Formalism.L2.Host.unif_spec (w.under (𝓞 F))
  set a := Formalism.L2.Host.atFin (w.under (𝓞 F)) (Formalism.L2.Host.unif (w.under (𝓞 F))) with ha_def
  have hx : Formalism.L2.Host.IsUnifAt w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE rfl hτ _
  have hx' : Formalism.L2.Host.IsUnifAt w' (Units.map (complMap hww.symm).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE hww.symm hτ' _
  rw [← UnrAt.locChar_eq_val hw hx, ← UnrAt.locChar_eq_val hw' hx']
  simp only [locChar, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  have hP : locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) *
      locIdele F w' (Units.map (complMap hww.symm).toMonoidHom a) =
      ideleMap F E (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a))) := by
    apply Units.ext
    rw [Units.val_mul, ← sigR_locIdele hE rfl hww.symm hne a, ← GlobalTheory.Doubling.algebraMap_norm_eq hE]
    rfl
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  rw [hP, hall η hη, hη.2.2.1, one_pow, map_one]

end GlobalTheory.LFun.SplitVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConj
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.RadRedLift

theorem exists_lift_unipRad (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (v : GL n 𝓀[k]) (hv : v ∈ unipRad 𝓀[k] e) :
    ∃ w : KO k n, (w : GL n k) ∈ unipRad k e ∧ GlobalTheory.LocGL.redK k n w = v := by
  classical
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((v : Matrix n n 𝓀[k]) i j)
  let B : Matrix n n 𝒪[k] := Matrix.of fun i j => if blk e i < blk e j then A i j else (1 : Matrix n n 𝒪[k]) i j
  have h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = v := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, B, Matrix.of_apply]
    split_ifs with hij
    · exact hA i j
    · rw [CuspMax.mem_unipRad_iff_entries.1 hv i j hij]
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  have hd : IsUnit B.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]
    exact (Matrix.GeneralLinearGroup.det v).ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨GlobalTheory.LocGL.toKO k n u, CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_, Units.ext ?_⟩
  · change algebraMap 𝒪[k] k ((u : Matrix n n 𝒪[k]) i j) = _
    rw [hu]
    simp only [B, Matrix.of_apply, if_neg hij, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [GlobalTheory.LocGL.redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [← h1, ← hu]; rfl

theorem red_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {r a b : ℕ} (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  intro k _ _ _ _ r a b h g₀
  obtain ⟨k₀, p, hp, rfl⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r g₀
  let κ : KO k (Fin r) := ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀, k₀, rfl⟩
  have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi => hp (show j < i from by
    rw [Fin.lt_def]; omega)
  refine ⟨GlobalTheory.LocGL.redK k (Fin r) κ, fun v hv => ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_lift_unipRad k _ v hv
  refine ⟨(κ * w * κ⁻¹ : KO k (Fin r)), (κ * w * κ⁻¹).2, ?_, ?_⟩
  · rw [mem_conjBy]
    have hn := parab_le_normalizer k _ (inv_mem hpP)
    have := (Subgroup.mem_normalizer_iff.1 hn (w : GL (Fin r) k)).1 hw
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ : GL (Fin r) k) * p)⁻¹ *
        ((κ * w * κ⁻¹ : KO k (Fin r)) : GL (Fin r) k) * (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ * p) =
        p⁻¹ * w * p⁻¹⁻¹ := by
      change ((κ : GL (Fin r) k) * p)⁻¹ * ((κ : GL (Fin r) k) * w * (κ : GL (Fin r) k)⁻¹) * ((κ : GL (Fin r) k) * p) = _
      group
    rw [e]
    exact this
  · rw [← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.RadRedLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_complexSide_of_hilbert_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  first | exact @GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | exact GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | (intros; apply GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → infPart D e = 0 → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ Φ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) := by
  first | exact @GlobalTheory.SchrTheta.isTheta_placeModel | exact GlobalTheory.SchrTheta.isTheta_placeModel | (intros; apply GlobalTheory.SchrTheta.isTheta_placeModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleEStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  first | exact @GlobalTheory.VecInv.tendsto_truncation | exact GlobalTheory.VecInv.tendsto_truncation | (intros; apply GlobalTheory.VecInv.tendsto_truncation <;> assumption)
end

