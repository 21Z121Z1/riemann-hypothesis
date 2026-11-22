import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

theorem csq_extend {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ : Type*} [Fintype κ] (c : κ → ℂ) (v : κ → V) :
    csq (extend hι h) τ c (fun i => ι (v i)) = csq h (τ.comp j) c v := by
  simp only [csq, form_extend]

theorem cnrm_extend_comb {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ μ : Type*} [Fintype κ] [Fintype μ] (c : κ → ℂ) (a : κ → μ → E) (v : μ → V) :
    cnrm (extend hι h) τ c (fun i => ∑ l, a i l • ι (v l)) =
      cnrm h (τ.comp j) (fun l => ∑ i, c i * τ (a i l)) v :=
  congrArg Real.sqrt ((csq_comb _ _ _ _ _).trans (csq_extend hι h τ _ v))

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem normAt_baseChange (τ : E →+* ℂ) (u : Fin T.N → F) :
    (T.baseChange E).normAt τ (fun j => algebraMap F E (u j)) = T.normAt (τ.comp (algebraMap F E)) u := rfl

theorem NormsLe.baseChange (h : T.NormsLe) : (T.baseChange E).NormsLe :=
  fun k τ => (normAt_baseChange E τ (T.w.col k)).trans_le (h k _)

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

theorem meanLog_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] (β : (F →+* ℂ) → ℝ) :
    meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β := by
  have h₁ : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [meanLog, meanLog, ← Module.finrank_mul_finrank ℚ F E, Nat.cast_mul,
    Adelic.HeightExt.sum_comp_algebraMap fun σ => Real.log (β σ), mul_comm (Module.finrank ℚ F : ℝ),
    mul_div_mul_left _ _ h₁]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

def chartAdj₂ (j : ℕ) : ChartPull ((G.baseChange E).adj₂ j) (G.adj₂ j) (G.fst E) :=
  chartPullTwist (chartPullTens (GlobalTheory.chartPullPull G.K.bundle _) (GlobalTheory.chartPullPull G.L₂ _))
    (GlobalTheory.chartPullPull G.L _) (j + G.D)

def toExt₂ (j : ℕ) : H0 G.str (G.adj₂ j) ⊤ →ₛₗ[algebraMap F E]
    H0 (G.baseChange E).str ((G.baseChange E).adj₂ j) ⊤ :=
  pullChart (G.chartAdj₂ E j) (G.isPullback_fst E).w le_top

theorem isExtension_toExt₂ (j : ℕ) : IsExtension (G.toExt₂ E j) :=
  isExtension_pullChart_top (G.isPullback_fst E) (isLB_tw (isLB_tens G.K.isLB G.isLB₂) G.isLB _)
    (isLB_tw (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLB₂) (G.baseChange E).isLB _)
    (G.chartAdj₂ E j) G.geom.alg.variety.proj (G.baseChange E).geom.alg.variety.proj

theorem toExt_mulE (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) :
    G.toExt E j (G.mulE j f) = (G.baseChange E).mulE j (G.toExt₂ E j f) := by
  refine (restr_pullChart (G.chartAdj E j) (G.isPullback_fst E).w (W := ⊤) le_top le_rfl le_top le_top _).symm.trans
    (congrArg _ ?_)
  refine (pullChart_mul _ (quotChart (G.baseChange E).K.isLB (G.baseChange E).isLBA (G.baseChange E).isLB₂
    (G.baseChange E).isLB rfl) (chartPullQuot (GlobalTheory.chartPullPull G.LA (G.fst E))
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) _)) (G.chartAdj₂ E j) (G.chartAdj E j)
    (fun t => ⟨(t.1 PUnit.unit, t.2.1 PUnit.unit, t.2.2.1 PUnit.unit, t.2.2.2 PUnit.unit), rfl, rfl, rfl⟩)
    _ le_top _ f).trans ?_
  exact congrArg (fun s => ProdChart.mul _ s _) (pullChart_ofSec _ _ _ G.e)

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]

variable (X) in

theorem toExtV_inclE {j : ℕ} (hj : j ≤ X.T) (f : H0 X.str (X.adj₂ j) ⊤) :
    X.toExtV E j (X.inclE hj f) = (X.baseChange E).inclE hj (X.toExt₂ E j f) :=
  Subtype.ext (X.toExt_mulE E j f)

variable (X) in

theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩

variable {E} in

theorem MulStable.mulBoundAt_baseChange (h : X.MulStable) {τ : E →+* ℂ} {β : ℝ}
    (hb : X.MulBoundAt (τ.comp (algebraMap F E)) β) : (X.baseChange E).MulBoundAt τ β := by
  intro j hj u m c f g e
  let b := Module.finBasis F (X.V j)
  let b' := (X.isExtension_extMap E j).basis b
  let G : Fin X.N × Fin _ → X.V (j + 1) := fun t => ⟨_, h.mem hj (Pi.single t.1 1) (b t.2)⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExtV E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have hG (t) : (X.toExtV E (j + 1) (G t) : (X.baseChange E).Sec (j + 1)) =
      (X.baseChange E).mulW j (Pi.single t.1 1) (X.toExtV E j (b t.2)) :=
    (X.toExt_mulW E j _ _).trans (congrArg (fun w => (X.baseChange E).mulW j w _)
      (funext fun l : Fin X.N => (by simp [Pi.single_apply] :
        algebraMap F E (Pi.single (M := fun _ => F) t.1 1 l) = Pi.single (M := fun _ => E) t.1 1 l)))
  change Fin X.N → ℂ at u
  obtain rfl : g = fun t : Fin X.N × Fin m => ∑ s, (if s.1 = t.1 then a t.2 s.2 else 0) • X.toExtV E (j + 1) (G s) :=
    funext fun t : Fin X.N × Fin m => Subtype.ext <| (e t.1 t.2).trans <| by
      simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hG]
  refine (cnrm_extend_comb (X.isExtension_extMap E (j + 1)) _ τ _ _ G).trans_le
    (le_of_eq_of_le (congrArg (cnrm _ _ · G) (funext fun s => ?_))
    ((hb j hj u _ (fun l => ∑ i, c i * τ (a i l)) b G fun _ _ => rfl).trans_eq
      (congrArg _ (cnrm_extend_comb (X.isExtension_extMap E j) _ τ c a b).symm)))
  change ∑ t : Fin X.N × Fin m, u t.1 * c t.2 * τ (if s.1 = t.1 then a t.2 s.2 else 0) = _
  simp [Fintype.sum_prod_type, apply_ite τ, Finset.mul_sum, mul_assoc]

theorem MulStable.mulBound_baseChange (h : X.MulStable) {β : (F →+* ℂ) → ℝ} (hb : ∀ σ, X.MulBoundAt σ (β σ)) :
    (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E)) :=
  (h.baseChange E).mulBound fun _ => h.mulBoundAt_baseChange (hb _)

variable (X) in

theorem latRank_M_baseChange (j : ℕ) : latRank E ((X.baseChange E).M j) = latRank F (X.M j) := by
  rw [latRank_M, latRank_M, finrank_V_baseChange]

theorem ShortFamily.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (X.baseChange E).ShortFamily j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  exact ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e),
    fun i τ => (X.nrm_toExtV E j τ _).trans_le (h₃ _ _)⟩

theorem ShortFamilyMean.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamilyMean j Λ) :
    (X.baseChange E).ShortFamilyMean j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  refine ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e), fun i => le_of_eq_of_le ?_ (h₃ (i.cast e))⟩
  exact (congrArg _ (funext fun τ => X.nrm_toExtV E j τ _)).trans
    (meanLog_baseChange E fun σ => (X.nm j).nrm σ (v (i.cast e)))

variable (X) in

theorem baseChange_mul_short :
    (∀ j u f, X.toExt E (j + 1) (X.mulW j u f) =
      (X.baseChange E).mulW j (algebraMap F E ∘ u) (X.toExt E j f)) ∧
    (∀ j f, X.toExt E j (X.mulE j f) = (X.baseChange E).mulE j (X.toExt₂ E j f)) ∧
    (X.MulStable → (X.baseChange E).MulStable) ∧
    (X.MulStable → ∀ (τ : E →+* ℂ) β, X.MulBoundAt (τ.comp (algebraMap F E)) β → (X.baseChange E).MulBoundAt τ β) ∧
    (X.MulStable → ∀ β : (F →+* ℂ) → ℝ, (∀ σ, X.MulBoundAt σ (β σ)) →
      (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E))) ∧
    (∀ j Λ, X.ShortFamily j Λ → (X.baseChange E).ShortFamily j Λ) ∧
    (∀ j Λ, X.ShortFamilyMean j Λ → (X.baseChange E).ShortFamilyMean j Λ) ∧
    (X.NormsLe → (X.baseChange E).NormsLe) ∧
    ∀ β : (F →+* ℂ) → ℝ, meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β :=
  ⟨X.toExt_mulW E, X.toExt_mulE E, fun h => h.baseChange E, fun h _ _ => h.mulBoundAt_baseChange,
    fun h _ => h.mulBound_baseChange E, fun _ _ h => h.baseChange E, fun _ _ h => h.baseChange E,
    fun h => h.baseChange E, meanLog_baseChange E⟩

end Data

end GlobalTheory.HilbertSamuel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.QuadT

section Abstract

variable {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (u l : ι → κ → A)

theorem core_term (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (a b : ι) (i j k : κ) :
    u a k * l a i * (u b j * l b k) =
      u a k * l b k * (l a i * u b j) - if k = j then u a k * l a i else 0 := by
  have e1 : u b j * l b k = l b k * u b j - if k = j then 1 else 0 := by
    rw [h b k j]; abel
  have e2 : u a k * l a i * (l b k * u b j) = u a k * l b k * (l a i * u b j) := by
    calc _ = u a k * (l a i * l b k) * u b j := by simp only [mul_assoc]
      _ = u a k * (l b k * l a i) * u b j := by rw [hll]
      _ = _ := by simp only [mul_assoc]
  rw [e1, mul_sub, e2]
  split_ifs <;> simp

theorem core1 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (i j : κ) :
    ∑ k, (∑ a, u a k * l a i) * (∑ b, u b j * l b k) =
      (∑ a, ∑ b, (∑ k, u a k * l b k) * (l a i * u b j)) -
        (Fintype.card ι : ℂ) • ∑ a, u a j * l a i := by
  simp only [Finset.sum_mul, Finset.mul_sum, core_term u l h hll, Finset.sum_sub_distrib]
  congr 1
  · calc (∑ k, ∑ b, ∑ a, u a k * l b k * (l a i * u b j))
          = ∑ b, ∑ k, ∑ a, u a k * l b k * (l a i * u b j) := Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ k, u a k * l b k * (l a i * u b j) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

theorem core2 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0) (i j : κ) :
    ∑ a, l a i * u a j = ∑ a, u a j * l a i + if i = j then (Fintype.card ι : ℂ) • (1 : A) else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

end Abstract

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

section Main

variable {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (u l : ι → κ → Module.End ℂ V) (E : ι → ι → Module.End ℂ V) (G : κ → κ → Module.End ℂ V)

theorem quad_main (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c)
    (hE : ∀ a b, E a b = ∑ c, u a c * l b c + (if a = b then (Fintype.card κ : ℂ) / 2 else 0) • 1)
    (hG : ∀ c d, G c d = ∑ a, u a c * l a d + (if c = d then (Fintype.card ι : ℂ) / 2 else 0) • 1)
    (x : ℂ) (i j : κ) :
    qop (fun c d => -G d c) ((Fintype.card κ : ℂ) / 2 - x)
        ((Fintype.card ι : ℂ) ^ 2 / 4 + (x - (Fintype.card κ : ℂ) / 2) * (Fintype.card ι : ℂ) / 2) i j =
      ∑ a, ∑ b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) := by
  have hR : ∀ a b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) =
      (∑ c, u a c * l b c) * (l a i * u b j) +
        (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) := by
    intro a b
    rw [hE]
    split_ifs <;> simp [add_mul, sub_mul, sub_smul, smul_mul_assoc, add_sub_assoc]
  simp only [hR, Finset.sum_add_distrib]
  have hD : ∑ a, ∑ b, (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) =
      ((Fintype.card κ : ℂ) / 2 - x) • ∑ a, l a i * u a j := by
    simp [ite_smul, Finset.sum_ite_eq, Finset.smul_sum]
  have h1 := core1 u l h hll i j
  rw [eq_sub_iff_add_eq] at h1
  rw [hD, core2 u l h, ← h1]
  simp only [qop, hG]
  simp only [neg_mul_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Finset.sum_add_distrib, ite_smul, zero_smul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    module
  · simp only [hij, Ne.symm hij, if_false]
    module

end Main

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

theorem fockAct1_Eab_eq {P Q R S : ℕ} (a b : Ix P Q) :
    fockAct1 P Q R S (Eab a b) =
      ∑ c, raiB (a, c) * lowB (b, c) + (if a = b then (Fintype.card (Ix R S) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct1_Eab]
  simp only [omE, Prod.mk.injEq, and_true, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem fockAct2_Eab_eq {P Q R S : ℕ} (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) =
      ∑ a, raiB (a, c) * lowB (a, d) + (if c = d then (Fintype.card (Ix P Q) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct2_Eab]
  simp only [omE, Prod.mk.injEq, true_and, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem negT_fockAct2_quad : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f,
    qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  intro P Q R S x
  refine ⟨(Fintype.card (Ix R S) : ℂ) / 2 - x,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 + (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2,
    fun i j f => ?_⟩
  have key : qop (negT (units (fockAct2 P Q R S))) ((Fintype.card (Ix R S) : ℂ) / 2 - x)
      ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 +
        (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2) i j =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab a b) - (if a = b then x else 0) • 1) *
        (lowB (a, i) * raiB (b, j)) :=
    quad_main (fun (a : Ix P Q) (c : Ix R S) => raiB (a, c)) (fun a c => lowB (a, c))
      (fun a b => fockAct1 P Q R S (Eab a b)) (fun c d => fockAct2 P Q R S (Eab c d))
      (fun b c e => by simp [GlobalTheory.FockCasimir.lowB_mul_raiB])
      (fun a c b e => GlobalTheory.FockCasimir.lowB_comm _ _) fockAct1_Eab_eq fockAct2_Eab_eq x i j
  rw [key, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [Module.End.mul_apply]
  apply Submodule.subset_span
  refine ⟨Eab a b, (lowB (a, i) * raiB (b, j)) f, ?_⟩
  by_cases hab : a = b
  · subst hab
    simp [Eab, Matrix.trace_single_eq_same]
  · simp [hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

end GlobalTheory.HoweR.QuadT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubschemeClosedBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem openSubscheme_closedFibre_lift (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R')
    (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens)
    (hφ : Function.Surjective φ) (h : IsPullback π f' f (spMap φ)) :
    ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧
      IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  have hsp : IsClosedImmersion (spMap φ) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have hπ : IsClosedImmersion π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) h.flip hsp
  obtain ⟨t, ht, hts⟩ :=
    (IsClosedImmersion.isClosedEmbedding π).isInducing.isOpen_iff.mp U.isOpen
  let W : X.Opens := ⟨t, ht⟩
  have hW : π ⁻¹ᵁ W = U := Opens.ext hts
  subst hW
  refine ⟨W, π ∣_ W, morphismRestrict_ι π W, ?_⟩
  exact IsPullback.paste_vert (isPullback_morphismRestrict π W) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCusp
section
noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem orbK_eq_twOrbU {G : Type} [Group G] (K0 : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K0 γ f =
      GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id G) γ ⊓ K0) f := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum
  refine finsum_congr fun q => ?_
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']
  simp only [MonoidHom.id_apply, GlobalTheory.LKCount.vol, GlobalTheory.LKLoc.volRat, GlobalTheory.LKLoc.locPart]
  congr 1
  push_cast
  rw [inv_div]

end GlobalTheory.OrbDesc

namespace GlobalTheory.LKCount

theorem orbK_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKCount.orbK (MonoidHom.id (GL ι K)) K0 γ f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 hK0o hK0c hbi
  rw [GlobalTheory.OrbDesc.orbK_eq_twOrbU K0 γ f hbi]
  exact GlobalTheory.OrbDesc.twOrbU_eq_zero_of_cusp K ι f hlc hcs hyp γ hsep hirr K0 K0 hK0o hK0c hK0o hK0c hbi

end GlobalTheory.LKCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingDefiniteBaseVanishOfMiStar2
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Div

theorem pairing_definite_base_vanish_of_miStar2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE → CxData.BtVanish (fc := F.fc) (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hsep hC hP sEE hM
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  obtain ⟨d, hU, hI, -⟩ := hM
  exact CxData.base_tuple_vanishing_of_hypotheses _ F.cr F.cv hR.jIsoR (hR.levs true).1 (hR.levs true).2.1 (hR.levs true).2.2
    (definite_coordinates_in_good_part _ true) (EvTie.evTie_of_ok hOk F _) hU hI

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinsFixHalf

theorem pb_eq_of_pins : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → LawsJ T → (∀ i, OMPins T R κ v₀ O i) → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR hT hO
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR
    ((hO ⟨0, lt_of_lt_of_le (by norm_num) D.R.two_le_m⟩).2.tuple ()).half

end GlobalTheory.PinsFixHalf
end

