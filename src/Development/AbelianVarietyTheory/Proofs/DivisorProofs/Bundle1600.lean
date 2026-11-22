import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped RealInnerProductSpace

noncomputable section

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def pt (a : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def fstH : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def sndH : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

theorem pt_ext {x y : AdeleRing (𝓞 F) F} (h1 : fstH x = fstH y) (h2 : sndH x = sndH y) : x = y :=
  Prod.ext h1 h2

theorem dot_infE_infE {κ : Type} [Fintype κ] (z y : κ → mixedEmbedding.mixedSpace F) :
    infE F z ⬝ᵥ infE F y = pt (∑ i, z i * y i) := by
  refine pt_ext ?_ ?_
  · simp only [dotProduct, map_sum, map_mul]
    show ∑ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (∑ i, z i * y i)
    simp only [map_sum, map_mul]
  · simp only [dotProduct, map_sum, map_mul]
    show ∑ i, (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    simp

theorem invOf_two_mul_pt (S : mixedEmbedding.mixedSpace F) :
    ∃ t, ⅟(2 : AdeleRing (𝓞 F) F) * pt S = pt t ∧ t + t = S := by
  set c : InfiniteAdeleRing F := fstH (⅟(2 : AdeleRing (𝓞 F) F))
  refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F (c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S), ?_, ?_⟩
  · refine pt_ext ?_ ?_
    · rw [map_mul]
      show c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
      rw [RingEquiv.symm_apply_apply]
    · rw [map_mul]
      show _ * (0 : FiniteAdeleRing (𝓞 F) F) = 0
      exact mul_zero _
  · have hc : c * 2 = 1 := by
      have h := congrArg fstH (invOf_mul_self (2 : AdeleRing (𝓞 F) F))
      rwa [map_mul, map_ofNat, map_one] at h
    rw [← map_add, ← add_mul, ← mul_two, hc, one_mul, RingEquiv.apply_symm_apply]

theorem schrInf_eq (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a))
    {κ : Type} [Fintype κ] (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    schrInf F ψ v φ z = Complex.exp (2 * Real.pi * Complex.I *
      (β (∑ i, z i * v.2 i) + β (∑ i, v.1 i * v.2 i) / 2)) * φ (z + v.1) := by
  have hψ' : ∀ a, ψ (pt a) = Complex.exp (2 * Real.pi * Complex.I * β a) := hψ
  obtain ⟨t, ht, htt⟩ := invOf_two_mul_pt (F := F) (∑ i, v.1 i * v.2 i)
  have hsum : ∀ a b : mixedEmbedding.mixedSpace F, pt (F := F) a + pt b = pt (a + b) := by
    intro a b
    refine pt_ext ?_ ?_
    · rw [map_add]
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · rw [map_add]
      exact add_zero (0 : FiniteAdeleRing (𝓞 F) F)
  have hbt : β t = β (∑ i, v.1 i * v.2 i) / 2 := by
    rw [← htt, map_add]; ring
  show ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * φ (z + v.1) = _
  rw [dot_infE_infE, dot_infE_infE, ht, hsum, hψ', map_add, hbt]
  push_cast
  ring_nf

end GlobalTheory.WeilAdm.RealModel

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def bil (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z y => β (∑ i, z i * y i))
    (fun z z' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun c z y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun z y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c z y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem bil_apply (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ]
    (z y : κ → mixedEmbedding.mixedSpace F) : bil β κ z y = β (∑ i, z i * y i) := rfl

def qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := (InnerProductSpace.toDual ℝ _).symm
    (LinearMap.toContinuousLinearMap (((bil β κ).flip y).comp (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] _).toLinearMap))
  map_add' y y' := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' c y := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

theorem inner_qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) (y : κ → mixedEmbedding.mixedSpace F)
    (x : EuclideanSpace ℝ (Fin n)) : ⟪qmap β Q y, x⟫ = bil β κ (Q x) y := by
  simp [qmap, InnerProductSpace.toDual_symm_apply]

theorem qmap_injective (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    Function.Injective (qmap β Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨b, hb⟩ := hβ (y i) hi
  have h := inner_qmap β Q y (Q.symm (Pi.single i b))
  rw [hy, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, bil_apply] at h
  have hs : ∑ j, (Pi.single i b : κ → mixedEmbedding.mixedSpace F) j * y j = y i * b := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [mul_comm]
  rw [hs] at h
  exact hb h.symm

def qEquiv (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.linearEquivOfInjective (qmap β Q) (qmap_injective β hβ Q) Q.toLinearEquiv.finrank_eq.symm

theorem qmap_qEquiv_symm (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
    (q : EuclideanSpace ℝ (Fin n)) : qmap β Q ((qEquiv β hβ Q).symm q) = q := by
  exact (qEquiv β hβ Q).apply_symm_apply q

def Peq {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V)
    (Y : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V) : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] V × V where
  toFun w := (Q (GlobalTheory.RealWeil.pPart w), Y (GlobalTheory.RealWeil.qPart w))
  invFun p := Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))
  map_add' w w' := by simp [GlobalTheory.RealWeil.pPart_add, GlobalTheory.RealWeil.qPart_add]
  map_smul' c w := by simp [GlobalTheory.RealWeil.pPart_smul, GlobalTheory.RealWeil.qPart_smul]
  left_inv w := by
    funext j
    cases j <;> simp [GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart]
  right_inv p := by
    have h1 : GlobalTheory.RealWeil.pPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Q.symm p.1 := by
      simp [GlobalTheory.RealWeil.pPart]
    have h2 : GlobalTheory.RealWeil.qPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Y.symm p.2 := by
      simp [GlobalTheory.RealWeil.qPart]
    simp only [h1, h2, LinearEquiv.apply_symm_apply]

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  intro F _ _ ψ β hψ hβ κ _
  let Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) ≃L[ℝ]
      (κ → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin).toContinuousLinearEquiv
  let Y := (qEquiv β hβ Q).symm
  refine ⟨_, Q, Peq Q.toLinearEquiv Y, fun w φ => ?_⟩
  funext x
  have hq := qmap_qEquiv_symm β hβ Q (GlobalTheory.RealWeil.qPart w)
  have h1 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) x
  have h2 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) (GlobalTheory.RealWeil.pPart w)
  rw [hq, bil_apply] at h1 h2
  simp only [Function.comp_apply, GlobalTheory.RealWeil.rhoFun, GlobalTheory.RealWeil.phase]
  rw [schrInf_eq ψ β hψ]
  show Complex.exp (2 * Real.pi * Complex.I * (β (∑ i, Q x i * Y (GlobalTheory.RealWeil.qPart w) i) +
      β (∑ i, Q (GlobalTheory.RealWeil.pPart w) i * Y (GlobalTheory.RealWeil.qPart w) i) / 2)) *
      φ (Q x + Q (GlobalTheory.RealWeil.pPart w)) = _
  rw [← h1, ← h2, ← map_add, real_inner_comm (GlobalTheory.RealWeil.pPart w)]
  congr 2
  push_cast
  ring

end GlobalTheory.WeilAdm.RealModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameExp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_phi {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem phi_eq_of_eq {D : Datum H} {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field firstFiveLaws.1.serre m' m

end GlobalTheory.Dict.SameExp

set_option maxHeartbeats 1000000 in
open GlobalTheory.Dict.SameFibre GlobalTheory.Dict.SameExp GlobalTheory.UnifPoint GlobalTheory.AnVal in

theorem GlobalTheory.Dict.anFib_ex_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ z, (A'.ex z).left = (A.ex z).left := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm' z
  have hyy : y'.x = y.x := anFib_point_eq E H Dw l Xo c hA r g X bas idx e x L y y' A A' hs hx hL mk hmk hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k, hk⟩ := exists_objMap_phi o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', hk'⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  have hφ := phi_eq_of_eq ((Category.id_comp _).trans hyy) n₁ k'
  have e₁ := congrArg (fun q => q.left) (k₁ z)
  have e₂ := congrArg (fun q => q.left) (k₂ z)
  refine e₂.symm.trans (Eq.trans ?_ e₁)
  refine (f₂ z).symm.trans (Eq.trans ?_ (f₁ z))
  rw [← hm₀ z, Category.assoc, ← hk, ← hk', hφ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  first | exact @GlobalTheory.SiegelPtAt.exists_ptAt | exact GlobalTheory.SiegelPtAt.exists_ptAt | (intros; apply GlobalTheory.SiegelPtAt.exists_ptAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecDetDualTensorSupport
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineHomSec

variable {X : Scheme.{0}} {F Q : X.Modules} {U V W : X.Opens}

theorem eq_repr_smul (c : Chart F 1) (h : W ≤ c.U) (x : Γ(F, W)) :
    x = (c.isFrame.basis h).repr x 0 • resM F h (c.e 0) := by
  have := (c.isFrame.basis h).sum_repr x
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem smul_cancel (c : Chart F 1) (h : W ≤ c.U) {a b : Γ(X, W)}
    (e : a • resM F h (c.e 0) = b • resM F h (c.e 0)) : a = b := by
  rw [← c.isFrame.basis_apply h] at e
  have := congrArg (fun x => (c.isFrame.basis h).repr x 0) e
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using this

theorem resM_frame (c c' : Chart F 1) (h : W ≤ c.U) (h' : W ≤ c'.U) :
    resM F h' (c'.e 0) = resG X (le_inf h h') ((det F 1).g c c').val • resM F h (c.e 0) := by
  have e : ((det F 1).g c c').val = (c.isFrame.basis (inf_le_left : c.U ⊓ c'.U ≤ c.U)).repr
      (resM F inf_le_right (c'.e 0)) 0 := by
    refine (c.isFrame.val_detUnit c'.isFrame inf_le_left inf_le_right).trans ?_
    rw [Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply]
  have := congrArg (resM F (le_inf h h'))
    (eq_repr_smul c (inf_le_left : c.U ⊓ c'.U ≤ c.U) (resM F inf_le_right (c'.e 0)))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [e]
  exact this

variable (s : F ⟶ Q)

def coef (c' : Chart F 1) (c : Chart Q 1) : Γ(X, c'.U ⊓ c.U) :=
  (c.isFrame.basis inf_le_right).repr (resM Q inf_le_left (s.app c'.U (c'.e 0))) 0

theorem app_frame (c' : Chart F 1) (c : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U) :
    s.app W (resM F h' (c'.e 0)) = resG X (le_inf h' h) (coef s c' c) • resM Q h (c.e 0) := by
  have := congrArg (resM Q (le_inf h' h))
    (eq_repr_smul c (inf_le_right : c'.U ⊓ c.U ≤ c.U) (resM Q inf_le_left (s.app c'.U (c'.e 0))))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [app_resM]
  exact this

theorem coef_trans (c' d' : Chart F 1) (c d : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U)
    (k' : W ≤ d'.U) (k : W ≤ d.U) :
    resG X (le_inf h' k') ((det F 1).g c' d').val * resG X (le_inf h' h) (coef s c' c) =
      resG X (le_inf h k) ((det Q 1).g c d).val * resG X (le_inf k' k) (coef s d' d) := by
  have e := app_frame s d' d k' k
  rw [resM_frame c' d' h' k', resM_frame c d h k, Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, smul_smul, smul_smul] at e
  rw [smul_cancel c h e, mul_comm]

def sec : (CechPic.tens (CechPic.dual (det F 1)) (det Q 1)).Sec where
  f i := coef s i.1 i.2
  compat i j := by
    have e := coef_trans s (W := (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U)) i.1 j.1 i.2 j.2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h : (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U) ≤ i.1.U ⊓ j.1.U := inf_le_inf inf_le_left inf_le_left
    exact ((res h ((det F 1).g i.1 j.1)).eq_inv_mul_iff_mul_eq.2 e).trans (mul_assoc _ _ _).symm

theorem eq_zero_of_coef (hF : IsVB F 1) (hQ : IsVB Q 1)
    (H : ∀ (c' : Chart F 1) (c : Chart Q 1) (z : X), z ∈ c'.U ⊓ c.U → coef s c' c = 0) : s = 0 := by
  ext V x
  choose U' e' hU' he' using hF
  choose U e hU he using hQ
  refine TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨Q.presheaf, Q.isSheaf⟩
    (fun z : V => V ⊓ (U' z ⊓ U z)) V (fun z => homOfLE inf_le_left)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hU' z, hU z⟩) (s.app V x) 0 fun z => ?_
  have h' : V ⊓ (U' z ⊓ U z) ≤ U' z := inf_le_right.trans inf_le_left
  have h : V ⊓ (U' z ⊓ U z) ≤ U z := inf_le_right.trans inf_le_right
  change resM Q inf_le_left (s.app V x) = resM Q inf_le_left 0
  rw [map_zero, ← app_resM, eq_repr_smul ⟨_, _, he' z⟩ h' (resM F _ x),
    Scheme.Modules.Hom.app_smul, app_frame s ⟨_, _, he' z⟩ ⟨_, _, he z⟩ h' h,
    H ⟨_, _, he' z⟩ ⟨_, _, he z⟩ z ⟨hU' z, hU z⟩, RingHom.map_zero, zero_smul, smul_zero]

theorem genericPoint_mem [IsIntegral X] (hF : IsVB F 1) (hQ : IsVB Q 1) (hs : s ≠ 0) :
    genericPoint X ∈ nonzeroLocus (sec s) := by
  by_contra hn
  refine hs (eq_zero_of_coef s hF hQ fun c' c z hz => ?_)
  have h := mt (mem_nonzeroLocus_iff (sec s) (c', c) (gen_mem hz)).2 hn
  refine basicOpen_eq_bot_iff (coef s c' c) |>.1 ?_
  by_contra hb
  obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty _).1 hb
  exact h (gen_mem hw)

theorem vanishesAt (hF : IsVB F 1) {z : X} (hz : z ∉ nonzeroLocus (sec s)) : VanishesAt s z := by
  intro U t e b hU he hb hzb
  obtain ⟨U', e', hU', he'⟩ := hF z
  let c' : Chart F 1 := ⟨_, _, he'⟩
  let c : Chart Q 1 := ⟨_, _, he⟩
  have hm : z ∈ c'.U ⊓ c.U := ⟨hU', hU⟩
  refine hz ((mem_nonzeroLocus_iff (sec s) (c', c) hm).2 ?_)
  have h' : c'.U ⊓ c.U ≤ c'.U := inf_le_left
  have h : c'.U ⊓ c.U ≤ c.U := inf_le_right
  have e₁ := congrArg (resM Q h) hb
  rw [← app_resM, eq_repr_smul c' h' (resM F _ t), Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, LB.resG_self, smul_smul, resM_smul] at e₁
  have e₂ := smul_cancel c h e₁
  have : z ∈ X.basicOpen (resG X h b) := by
    have := X.basicOpen_res b (homOfLE h).op
    exact this.ge ⟨hm, hzb⟩
  rw [← e₂, Scheme.basicOpen_mul] at this
  exact this.2

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem form_app (h : Met p σ Q 1) (c' : Chart F 1) (c : Chart Q 1) {y : CxPts p σ}
    (hy' : y ∈ ptsIn p σ c'.U) (hy : y ∈ ptsIn p σ c.U) :
    (h.form (s.app c'.U (c'.e 0)) (s.app c'.U (c'.e 0)) y).re =
      ‖ev p σ _ (coef s c' c) y‖ ^ 2 * (h.G c y).det.re := by
  have hW := mem_ptsIn_inf.2 ⟨hy', hy⟩
  rw [← h.form_resM _ _ inf_le_left hW, ← app_resM, app_frame s c' c inf_le_left inf_le_right,
    LB.resG_self, h.form_smul_left, ← h.conj_form, h.form_smul_left, map_mul, h.conj_form,
    h.form_resM _ _ _ hW, h.form_frame c hy, ← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.normSq_eq_norm_sq, Matrix.det_fin_one]

theorem exists_ratSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  intro k _ X p _ F Q g' g H' H s hs
  have hξ := genericPoint_mem s g'.isVB g.isVB hs
  let M := (VMetric.det H').dual.tens (VMetric.det H)
  let u : M.B.Sec := sec s
  refine ⟨ratOfSec u hξ, isRatSec_ratOfSec u hξ,
    fun z hz => vanishesAt s g'.isVB fun h => notMem_supp_divOfSec.2 h hz, ?_⟩
  intro σ y hy U t ht hU
  have hy' : y ∈ ptsIn p σ (nonzeroLocus u) := (offSupp_divOfSec (hL := M.isLB) (hs := hξ)).le hy
  let c' : Chart F 1 := ⟨_, _, ht⟩
  let c := g.isVB.pick y
  have hc : y ∈ ptsIn p σ c.U := g.isVB.mem_pick y
  have hi : y ∈ ptsIn p σ (M.B.U (c', c)) := mem_ptsIn_inf.2 ⟨hU, hc⟩
  have h0 : ev p σ _ (coef s c' c) y ≠ 0 := (secVal_ne_zero_iff u hi).2 hy'
  have hG := det_re_pos ((g.met σ).posDef c y hc)
  have hG' := det_re_pos ((g'.met σ).posDef c' y hU)
  have e : ((g.met σ).form (s.app U t) (s.app U t) y).re = _ := form_app s (g.met σ) c' c hU hc
  have e' : (g'.met σ).form t t y = ((g'.met σ).G c' y).det :=
    ((g'.met σ).form_frame c' hU 0 0).trans (Matrix.det_fin_one _).symm
  refine ⟨e ▸ by positivity, ?_⟩
  refine (logNorm_ratOfSec (s := u) (hs := hξ) (M.φ σ) hy').trans ?_
  rw [(M.φ σ).nsq_eq (secVal_mem u) hi, e, e']
  congr 2
  change ‖ev p σ _ (coef s c' c) y‖ ^ 2 * Real.exp (-(-(-Real.log ((g'.met σ).G c' y).det.re) +
    -Real.log ((g.met σ).G c y).det.re)) = _
  rw [neg_neg, ← sub_eq_add_neg, neg_sub, Real.exp_sub, Real.exp_log hG, Real.exp_log hG', mul_div_assoc]

end GlobalTheory.LineHomSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRelDim

theorem exists_relDim : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro K _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim K A hA

end GlobalTheory.AbVarRelDim
end

