import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterBlockSumEqDirectSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section FrobSS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem isFrobSS_sum {ρ₁ : Weil h → End ℂ V} {N₁ : End ℂ V} {a : WDRep h V}
    {ρ₂ : Weil h → End ℂ V'} {N₂ : End ℂ V'} {b : WDRep h V'}
    (ha : IsFrobSS ρ₁ N₁ a) (hb : IsFrobSS ρ₂ N₂ b) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (a.sum b) := by
  refine ⟨by rw [WDRep.sum_N, ha.1, hb.1], fun g => ?_⟩
  obtain ⟨c1, n1⟩ := ha.2 g
  obtain ⟨c2, n2⟩ := hb.2 g
  let R := LinearMap.prodMapRingHom ℂ V V'
  have e1 : (a.sum b).ρ g = R (a.ρ g, b.ρ g) := rfl
  have e2 : (ρ₁ g).prodMap (ρ₂ g) = R (ρ₁ g, ρ₂ g) := rfl
  show Commute ((a.sum b).ρ g) ((ρ₁ g).prodMap (ρ₂ g)) ∧ IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (a.sum b).ρ g)
  rw [e1, e2]
  have hc : Commute ((a.ρ g, b.ρ g) : End ℂ V × End ℂ V') (ρ₁ g, ρ₂ g) := Prod.ext c1.eq c2.eq
  refine ⟨hc.map R, ?_⟩
  rw [← map_sub]
  obtain ⟨m, hm⟩ := n1
  obtain ⟨n, hn⟩ := n2
  refine IsNilpotent.map ⟨m + n, Prod.ext ?_ ?_⟩ R
  · simp [pow_add, hm]
  · simp [pow_add, hn]

end FrobSS

section Tens

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' V'' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [AddCommGroup V''] [Module LL V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] LL V'']

theorem tensV_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P g (tensV P f z) = tensV P (g ∘ₗ f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_id (z : V ⊗[ℚ_[l]] Bst P) : tensV P (LinearMap.id : V →ₗ[LL] V) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_zero (z : V ⊗[ℚ_[l]] Bst P) : tensV P (0 : V →ₗ[LL] V') z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem tensV_add (f g : V →ₗ[LL] V') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P (f + g) z = tensV P f z + tensV P g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [add_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

end Tens

section Split

variable (k : Type) [Field k] (a b : ℕ)

def pr₁ : (Fin (a + b) → k) →ₗ[k] (Fin a → k) :=
  LinearMap.fst k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def pr₂ : (Fin (a + b) → k) →ₗ[k] (Fin b → k) :=
  LinearMap.snd k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def in₁ : (Fin a → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inl k _ _

def in₂ : (Fin b → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inr k _ _

theorem pr₁_in₁ : pr₁ k a b ∘ₗ in₁ k a b = LinearMap.id := by ext v <;> simp [pr₁, in₁]
theorem pr₂_in₁ : pr₂ k a b ∘ₗ in₁ k a b = 0 := by ext v <;> simp [pr₂, in₁]
theorem pr₁_in₂ : pr₁ k a b ∘ₗ in₂ k a b = 0 := by ext v <;> simp [pr₁, in₂]
theorem pr₂_in₂ : pr₂ k a b ∘ₗ in₂ k a b = LinearMap.id := by ext v <;> simp [pr₂, in₂]
theorem in_pr : in₁ k a b ∘ₗ pr₁ k a b + in₂ k a b ∘ₗ pr₂ k a b = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp only [pr₁, pr₂, in₁, in₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, ← map_add]
  apply (GlobalTheory.DirectSumLocal.splitEquiv k a b).injective
  simp

end Split

end GlobalTheory.Pst.SumOneField

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section WdLin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  [AddCommGroup V₃] [Module ↥LL.1 V₃] [Module ℚ_[l] V₃] [IsScalarTower ℚ_[l] ↥LL.1 V₃]
  {r₁ : Representation ↥LL.1 ↥(GK K) V₁} {r₂ : Representation ↥LL.1 ↥(GK K) V₂}
  {r₃ : Representation ↥LL.1 ↥(GK K) V₃}

theorem wdLin_comp_eq_id {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₁} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₁ x (g v)) (hgf : g ∘ₗ f = LinearMap.id) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = LinearMap.id :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => congrArg (wdMk P ι r₁) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_id P x.1))))

theorem wdLin_comp_eq_zero {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₃} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₃ x (g v)) (hgf : g ∘ₗ f = 0) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = 0 :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => (congrArg (wdMk P ι r₃) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_zero P x.1))))).trans
      (wdMk_zero P ι r₃)

end WdLin

section Iso

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)

theorem isFrobSS_wdRep {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (r : Representation ↥LL.1 ↥(GK Bw.Kw) V)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P r)] :
    IsFrobSS (wdRho P ι Bw h hj r) (wdN P ι r) (wdRep P ι Bw h hj r) := by
  obtain ⟨u, hN, hu, -, hc, hr⟩ := wdRep_spec P ι Bw h hj r
  rw [← hN]
  exact isFrobSS_of_unipotent u hu hc hr

variable {LL : FinExt l} {a b : ℕ} (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin (a + b) → ↥LL.1))
  (ρ₁ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin a → ↥LL.1)) (ρ₂ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin b → ↥LL.1))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)]
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso_sum
    (he : ∀ g v, GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b (ρ g v) =
      (ρ₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).1, ρ₂ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).2)) :
    (wdRep P ι Bw h hj ρ).Iso ((wdRep P ι Bw h hj ρ₁).sum (wdRep P ι Bw h hj ρ₂)) := by
  have hp₁ : ∀ g v, pr₁ (↥LL.1) a b (ρ g v) = ρ₁ g (pr₁ (↥LL.1) a b v) := fun g v => by
    simp only [pr₁, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.fst_apply]
  have hp₂ : ∀ g v, pr₂ (↥LL.1) a b (ρ g v) = ρ₂ g (pr₂ (↥LL.1) a b v) := fun g v => by
    simp only [pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.snd_apply]
  have hi₁ : ∀ g v, in₁ (↥LL.1) a b (ρ₁ g v) = ρ g (in₁ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₁]
  have hi₂ : ∀ g v, in₂ (↥LL.1) a b (ρ₂ g v) = ρ g (in₂ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₂]
  let Φ : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := (wdLin P ι hp₁).prod (wdLin P ι hp₂)
  let Ψ : WDSpace P ι ρ₁ × WDSpace P ι ρ₂ →ₗ[ℂ] WDSpace P ι ρ := (wdLin P ι hi₁).coprod (wdLin P ι hi₂)
  have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
    show wdLin P ι hi₁ (wdLin P ι hp₁ (wdMk P ι ρ x)) + wdLin P ι hi₂ (wdLin P ι hp₂ (wdMk P ι ρ x)) = wdMk P ι ρ x
    exact (wdMk_add P ι ρ _ _).symm.trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((Submodule.coe_add _ _).trans ((congrArg₂ (· + ·) (tensV_comp P (pr₁ (↥LL.1) a b) (in₁ (↥LL.1) a b) x.1)
      (tensV_comp P (pr₂ (↥LL.1) a b) (in₂ (↥LL.1) a b) x.1)).trans ((tensV_add P _ _ x.1).symm.trans
        ((congrArg (fun f => tensV P f x.1) (in_pr (↥LL.1) a b)).trans (tensV_id P x.1)))))))
  have c11 := wdLin_comp_eq_id P ι hi₁ hp₁ (pr₁_in₁ (↥LL.1) a b)
  have c22 := wdLin_comp_eq_id P ι hi₂ hp₂ (pr₂_in₂ (↥LL.1) a b)
  have c21 := wdLin_comp_eq_zero P ι hi₁ hp₂ (pr₂_in₁ (↥LL.1) a b)
  have c12 := wdLin_comp_eq_zero P ι hi₂ hp₁ (pr₁_in₂ (↥LL.1) a b)
  have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := LinearMap.ext fun y => Prod.ext
    (show wdLin P ι hp₁ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.1 from
      ((LinearMap.map_add (wdLin P ι hp₁) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c11 y.1)
        (LinearMap.congr_fun c12 y.2))).trans (add_zero y.1))
    (show wdLin P ι hp₂ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.2 from
      ((LinearMap.map_add (wdLin P ι hp₂) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c21 y.1)
        (LinearMap.congr_fun c22 y.2))).trans (zero_add y.2))
  let e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := LinearEquiv.ofLinear Φ Ψ hΦΨ hΨΦ
  have hρe : ∀ σ y, e (wdRho P ι Bw h hj ρ σ y) =
      ((wdRho P ι Bw h hj ρ₁ σ).prodMap (wdRho P ι Bw h hj ρ₂ σ)) (e y) := fun σ y =>
    Prod.ext (wdLin_wdRho P ι Bw h hj hp₁ σ y) (wdLin_wdRho P ι Bw h hj hp₂ σ y)
  have hNe : ∀ y, e (wdN P ι ρ y) = ((wdN P ι ρ₁).prodMap (wdN P ι ρ₂)) (e y) := fun y =>
    Prod.ext (wdLin_wdN P ι hp₁ y) (wdLin_wdN P ι hp₂ y)
  have h0 := isFrobSS_wdRep P ι Bw h hj ρ
  have h12 := isFrobSS_sum (isFrobSS_wdRep P ι Bw h hj ρ₁) (isFrobSS_wdRep P ι Bw h hj ρ₂)
  exact IsFrobSS.iso h0 h12 e hρe hNe

end Iso

theorem wdPst_sumRep : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) = (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a b s s' hV₁ hV₂ hV
  haveI := hV₁.finite
  haveI := hV₂.finite
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw h hj hV₁, wdPst_of_isPst ι Bw h hj hV₂, WD.lpSum_mk]
  exact WD.sound (wdRep_iso_sum P ι Bw h hj _ _ _ fun g v => GlobalTheory.DirectSumLocal.splitEquiv_sumRep s s' _ v)

end GlobalTheory.Pst.SumOneField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlarge
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.EnlargeParam

open GlobalTheory.Pst.EnlargeCoeff Module

section General

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
  {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂)) :
    (wdRep P ι Bw h hj ρ₁).Iso (wdRep P ι Bw h hj ρ₂) := by
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), dQ P hf (a • x) = s a • dQ P hf x := fun a x =>
    Subtype.ext (tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ := chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) (dQ P hf) hT (dQ_mulD P hf)
  have hΦρ : ∀ σ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y) := fun σ y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
      (dQ_weilD P Bw h hf σ) y
  have hΦN : ∀ y, Φ (wdN P ι ρ₁ y) = wdN P ι ρ₂ (Φ y) := fun y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (monD_mulD P ρ₁) _ (monD_mulD P ρ₂)
      (fun x => Subtype.ext (tensQ_onB P f _ x.1)) y
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
      exact (sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (dQ P (hπ j) x), chg_mk _ _ _ _ _ _ _ _ _ _⟩
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact IsFrobSS.iso (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₁)
    (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₂) (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) hΦρ hΦN

end General

theorem wdPst_enlarge {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) :
    IsPst P (Bw.repE L₁ r₁) →
    wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) =
      wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  intro hV₁
  have hV₂ := GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) =
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))
  rw [wdPst_of_isPst ι Bw h hj hV₂, wdPst_of_isPst ι Bw h hj hV₁]
  exact (WD.sound (wdRep_iso P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf
    (incV_smul hL) b π hπ' hsum hdim)).symm

end GlobalTheory.Pst.EnlargeParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrixStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  first | exact @GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | exact GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitConjVal

theorem eq_of_isEquiv {F : Type} [Field F] (v1 v2 : Valuation F (WithZero (Multiplicative ℤ)))
    (h : v1.IsEquiv v2) (a b : F) (ha : v1 a = WithZero.exp (-1)) (hb : v2 b = WithZero.exp (-1))
    (x : F) : v1 x = v2 x := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact WithZero.exp_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact WithZero.exp_ne_zero hb.symm
  have hlt : ∀ r s : F, v1 r < v1 s ↔ v2 r < v2 s := fun r s => by
    rw [← not_le, ← not_le, h s r]
  have hval : ∀ y : F, y ≠ 0 → v2 y = WithZero.exp (WithZero.log (v2 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have hval1 : ∀ y : F, y ≠ 0 → v1 y = WithZero.exp (WithZero.log (v1 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have ha2 : v2 a = WithZero.exp (-1) := by
    have h1 : v2 a < 1 := by
      rw [← map_one v2, ← hlt, map_one, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h2 : v1 b < 1 := by
      rw [← map_one v1, hlt, map_one, hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h3 : ¬ v1 b < v1 a := by
      intro h3
      rw [hlt, hb] at h3
      rw [hval a ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [hval a ha0, WithZero.exp_lt_exp] at h3
      omega
    have h4 : v1 b = v1 a := by
      rw [hval1 b hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [hval1 b hb0, ha, WithZero.exp_lt_exp] at h3
      rw [hval1 b hb0, ha, WithZero.exp_inj]
      omega
    rw [← hb]
    exact ((h.eq_iff).1 h4).symm
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set k := WithZero.log (v1 x)
  have e1 : v1 x = v1 (a ^ (-k)) := by
    rw [map_zpow₀, ha, ← WithZero.exp_zsmul, hval1 x hx]
    congr 1; simp [k]
  rw [e1, (h.eq_iff).1 e1, map_zpow₀, map_zpow₀, ha, ha2]

theorem valuation_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  intro L _ _ _ s c hc hci x
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have ho : IsOpenMap c :=
    AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc
  have hc' : Continuous c.symm := c.toEquiv.continuous_symm_iff.2 ho
  let v' : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)) :=
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).comap c.toRingHom
  have hE : v'.IsEquiv Valued.v := by
    rw [Valuation.isEquiv_iff_val_lt_one]
    intro y
    refine ⟨fun h => ?_, fun h => GlobalTheory.ConjParahoric.val_lt_one_map c.toRingHom hc h⟩
    simpa using GlobalTheory.ConjParahoric.val_lt_one_map c.symm.toRingHom hc' h
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  obtain ⟨ϖ, hϖ⟩ := s.w.valuation_exists_uniformizer L
  have h1 : v' (s.i ϖ) = WithZero.exp (-1) := by
    show Valued.v (c (s.i ϖ)) = _
    rw [hci, ReciprocityTheory.Aut.adic_valued_algebraMap, hϖ]
  have h2 : Valued.v (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) π) =
      WithZero.exp (-1) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  exact eq_of_isEquiv v' Valued.v hE _ _ h1 h2 x

end GlobalTheory.SplitConjVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjDense

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_of_agree : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  intro L _ _ _ s c hc hci μ ξ hμ ⟨N, hN⟩ hglob d
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

end GlobalTheory.ConjDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAddStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  first | exact @GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add | exact GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add | (intros; apply GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPairing_of_invariant_trilinear_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  first | exact @GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | exact GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | (intros; apply GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form <;> assumption)
end

