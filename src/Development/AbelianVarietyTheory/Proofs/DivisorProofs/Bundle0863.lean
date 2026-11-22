import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicFin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportC
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

section Act

variable {G : Type} [Monoid G]

def act (T : G →₀ ℂ) (f : G → ℂ) (g : G) : ℂ :=
  T.sum fun k c => c * f (g * k)

def comp (T T' : G →₀ ℂ) : G →₀ ℂ :=
  T.sum fun a c => T'.sum fun b d => Finsupp.single (a * b) (c * d)

@[simp] theorem act_zero (f : G → ℂ) (g : G) : act (0 : G →₀ ℂ) f g = 0 := by
  simp [act]

theorem act_add (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (T + T') f g = act T f g + act T' f g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

@[simp] theorem act_single (k : G) (c : ℂ) (f : G → ℂ) (g : G) :
    act (Finsupp.single k c) f g = c * f (g * k) :=
  Finsupp.sum_single_index (zero_mul _)

theorem act_finset_sum {ι : Type} (s : Finset ι) (T : ι → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (∑ i ∈ s, T i) f g = ∑ i ∈ s, act (T i) f g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, act_add, ih]

theorem act_finsupp_sum {α : Type} (T : α →₀ ℂ) (t : α → ℂ → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (T.sum t) f g = T.sum fun a c => act (t a c) f g :=
  act_finset_sum _ _ _ _

theorem act_comp (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (comp T T') f g = act T (act T' f) g := by
  unfold comp
  rw [act_finsupp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only
  rw [act_finsupp_sum]
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [Finsupp.sum_single_index (zero_mul _), mul_assoc, mul_assoc]

theorem act_congr (T : G →₀ ℂ) {f f' : G → ℂ} {g : G} (h : ∀ k ∈ T.support, f (g * k) = f' (g * k)) :
    act T f g = act T f' g :=
  Finset.sum_congr rfl fun k hk => by simp only; rw [h k hk]

theorem mem_support_comp {T T' : G →₀ ℂ} {k : G} (hk : k ∈ (comp T T').support) :
    ∃ a ∈ T.support, ∃ b ∈ T'.support, k = a * b := by
  classical
  unfold comp Finsupp.sum at hk
  obtain ⟨a, ha, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)
  obtain ⟨b, hb, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)
  exact ⟨a, ha, b, hb, Finset.mem_singleton.1 (Finsupp.support_single_subset hk)⟩

theorem exists_fin (T : G →₀ ℂ) : ∃ (n : ℕ) (h : Fin n → G) (c : Fin n → ℂ),
    (∀ i, h i ∈ T.support) ∧ ∀ f g, act T f g = ∑ i, c i * f (g * h i) := by
  classical
  refine ⟨T.support.card, fun i => (T.support.equivFin.symm i).1, fun i => T (T.support.equivFin.symm i).1,
    fun i => (T.support.equivFin.symm i).2, fun f g => ?_⟩
  unfold act Finsupp.sum
  rw [← Finset.sum_coe_sort T.support]
  exact Fintype.sum_equiv T.support.equivFin _ _ fun x => by simp

end Act

variable {F : Type} [NormedField F]

def cell {n : ℕ} (z : GL (Fin n) F) (U : Set (GL (Fin n) F)) : Set (GL (Fin n) F) :=
  {g | ∃ u ∈ unipB F (Fin n), ∃ k ∈ U, g = u * z * k}

def Cuts (ψ : AddChar F ℂ) {n : ℕ} (U X A : Set (GL (Fin n) F)) : Prop :=
  ∃ T : GL (Fin n) F →₀ ℂ, ∀ f : GL (Fin n) F → ℂ, Eqv ψ f → (∀ u ∈ U, ∀ g, f (g * u) = f g) →
    ∀ g ∈ A, act T f g = X.indicator f g

example (ψ : AddChar F ℂ) {n : ℕ} (U A : Set (GL (Fin n) F)) : Cuts ψ U Set.univ A :=
  ⟨Finsupp.single 1 1, fun f _ _ g _ => by simp⟩

end GlobalTheory.JSW.Cut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.NormIndex

open Neutral.B1

theorem mul_eq_one_of_card_two {G : Type} [Group G] [Finite G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  classical
  have hab : b = a := by
    by_contra hne
    haveI := Fintype.ofFinite G
    have : ({1, a, b} : Finset G).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair (Ne.symm hne), h] at this
    omega
  subst hab
  have := pow_card_eq_one' (G := G) (x := b)
  rw [h, pow_two] at this
  exact this

theorem mul_mem_range_norm (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ)
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  obtain ⟨b, -, -⟩ := hE.basis
  have h2 : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := Algebra.IsQuadraticExtension.isGalois F E
  let φ : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let L : IntermediateField F (AlgebraicClosure F) := φ.fieldRange
  let e : E ≃ₐ[F] L := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F L := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : IsGalois F L := IsGalois.of_algEquiv e
  have hL2 : Module.finrank F L = 2 := e.toLinearEquiv.finrank_eq.symm.trans h2
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [← hL2, ← IsGalois.card_aut_eq_finrank]
  have hab : IsFiniteAbelian F L :=
    { finiteDimensional := inferInstance
      isGalois := inferInstance
      comm := fun a b' => by
        haveI : Fact (Nat.card (L ≃ₐ[F] L)).Prime := ⟨hcard ▸ Nat.prime_two⟩
        haveI := isCyclic_of_prime_card (α := L ≃ₐ[F] L) (p := Nat.card (L ≃ₐ[F] L)) rfl
        exact IsCyclic.commGroup.mul_comm a b' }
  obtain ⟨Art, hArt⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero F
  obtain ⟨-, hker⟩ := hArt.2.2.2.2 L hab
  have hN : (Units.map (Algebra.norm F : E →* F)).range = normGroup F L := by
    ext z
    simp only [normGroup, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e : E →* L) w, Units.ext (Algebra.norm_eq_of_algEquiv e (w : E))⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e.symm : L →* E) w, Units.ext (Algebra.norm_eq_of_algEquiv e.symm (w : L))⟩
  rw [hN, ← hker] at hx hy ⊢
  rw [MonoidHom.mem_ker] at hx hy ⊢
  rw [map_mul]
  haveI : Finite (L ≃ₐ[F] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact mul_eq_one_of_card_two hcard hx hy

end GlobalTheory.KSp.NormIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurPolar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_of_diag (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a b s t : ℂ} (ha : IsMultIP M μ 𝓕 T T a) (hb : IsMultIP M μ 𝓕 T' T' b)
    (hs : IsMultIP M μ 𝓕 (T + T') (T + T') s)
    (ht : IsMultIP M μ 𝓕 (T + Complex.I • T') (T + Complex.I • T') t) :
    IsMultIP M μ 𝓕 T T' ((1 / 2) * ((s - a - b) - Complex.I * (t - a - b))) := by
  intro v v'
  obtain ⟨ia, ea⟩ := ha v v'
  obtain ⟨ib, eb⟩ := hb v v'
  obtain ⟨is, es⟩ := hs v v'
  obtain ⟨it, et⟩ := ht v v'
  have e : (fun g => star (T v g) * T' v' g) =
      fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
        - star (T v g) * T v' g - star (T' v g) * T' v' g)) := by
    funext g
    show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g)
        - star (T v g) * T v' g - star (T' v g) * T' v' g))
    have hI : star Complex.I = - Complex.I := by simp
    rw [star_add, star_add, star_mul, hI]
    have h2 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g
      - Complex.I * star (T' v g) * T' v' g) * h2
  have i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕) :=
    is.sub ia
  have i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
      - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i1.sub ib
  have i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g) (μ.restrict 𝓕) := it.sub ia
  have i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i3.sub ib
  have i5 := i4.const_mul Complex.I
  rw [e]
  refine ⟨(i2.sub i5).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib,
    integral_sub is ia, integral_sub it ia, ea, eb, es, et]
  ring

theorem isMultiplicityInner_inner : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  intro D V S M μ 𝓕 HM U h x y
  have hip := h.2.2
  have hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := hip z z
      unfold ipM at this
      rw [dif_neg hn] at this
      exact hz (inner_self_eq_zero.1 this)
  rw [hip]
  apply ipM_spec
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add] at hs ht
  rw [map_smul] at ht
  exact ⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

end GlobalTheory.SchurPolar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
section
noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamily
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.BaseVacuum

theorem sum_posE {M : Type} [AddCommMonoid M] (n n' : ℕ) (f : Fin (n' * 2) → Fin (n * 2) → M) :
    ∑ i, ∑ j, f i j = ∑ p : (Fin n' × Fin n) × Fin 4, f (posE n n' p).1 (posE n n' p).2 := by
  rw [← Fintype.sum_prod_type']
  exact ((posE n n').sum_comp (fun x => f x.1 x.2)).symm

theorem putB_posE (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E)
    (p : (Fin n' × Fin n) × Fin 4) :
    putB D k x (posE n n' p).1 (posE n n' p).2 = if p.1 = k then x p.2 else 0 := by
  simp [putB]

theorem hYY_putB (D : D7) {n n' : ℕ} (k k' : Fin n' × Fin n) (x y : Fin 4 → D.host.E) :
    TaylorLogMetric.hYY D (putB D k x) (putB D k' y) =
      if k = k' then Algebra.trace D.host.K D.host.E (∑ a, x a * D.host.conj (y a)) else 0 := by
  unfold TaylorLogMetric.hYY
  rw [sum_posE]
  simp only [putB_posE]
  rw [Fintype.sum_prod_type]
  split_ifs with h
  · subst h
    rw [Fintype.sum_eq_single k]
    · simp
    · intro k'' hk
      simp [hk]
  · rw [Finset.sum_eq_zero, map_zero]
    intro k'' _
    apply Finset.sum_eq_zero
    intro a _
    by_cases h1 : k'' = k
    · subst h1
      simp [Ne.symm h, h]
    · simp [h1]

end GlobalTheory.BaseVacuum

namespace GlobalTheory.BaseVacuum

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem gamma_g_xv (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : B.γ₀.g (xv B w) = Pi.single w 1 := by
  simp [xv]

theorem trace_xv (B : Base D cc δ) (w w' : Fin 4 × D.what₂.Tau) :
    Algebra.trace D.host.K D.host.E (∑ a, xv B w a * D.host.conj (xv B w' a)) = if w = w' then 1 else 0 := by
  apply (algebraMap D.host.K D.host.E).injective
  have h := B.γ₀.isom (xv B w) (xv B w')
  rw [gamma_g_xv, gamma_g_xv] at h
  rw [map_sum, ← h]
  simp only [Pi.single_apply]
  by_cases hw : w = w'
  · subst hw
    simp
  · rw [if_neg hw, map_zero]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : u = w
    · subst hu
      simp [hw]
    · simp [hu]

theorem orthonormal_bas (B : Base D cc δ) (n n' : ℕ) : TaylorLogMetric.Orthonormal D (bas B n n') := by
  intro i j
  unfold bas
  rw [hYY_putB]
  by_cases hk : (ixE D n n' i).1 = (ixE D n n' j).1
  · rw [if_pos hk, map_sum]
    have := trace_xv B (ixE D n n' i).2 (ixE D n n' j).2
    rw [map_sum] at this
    rw [this]
    congr 1
    apply propext
    constructor
    · intro h
      exact (ixE D n n').injective (Prod.ext hk h)
    · intro h
      rw [h]
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (by rw [h])

set_option synthInstance.maxHeartbeats 200000 in

theorem sum_g_smul_xv (B : Base D cc δ) (y : Fin 4 → D.host.E) :
    ∑ w, B.γ₀.g y w • xv B w = y := by
  have h1 : ∑ w, B.γ₀.g y w • (Pi.single w (1 : D.host.K) : Fin 4 × D.what₂.Tau → D.host.K) = B.γ₀.g y := by
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ w, B.γ₀.g y w • xv B w = B.γ₀.g.symm (∑ w, B.γ₀.g y w • Pi.single w (1 : D.host.K)) := by
        simp only [map_sum, map_smul, xv]
    _ = y := by rw [h1, LinearEquiv.symm_apply_apply]

theorem matrix_eq_sum_putB (B : Base D cc δ) (n n' : ℕ) (M : Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E) :
    M = ∑ k : Fin n' × Fin n, ∑ w : Fin 4 × D.what₂.Tau,
      B.γ₀.g (fun a => M (posE n n' (k, a)).1 (posE n n' (k, a)).2) w • putB D k (xv B w) := by
  ext i j
  obtain ⟨p, hp⟩ := (posE n n').surjective (i, j)
  have hi : i = (posE n n' p).1 := by rw [hp]
  have hj : j = (posE n n' p).2 := by rw [hp]
  subst hi hj
  simp only [Matrix.sum_apply, Matrix.smul_apply, putB_posE, smul_ite, smul_zero]
  rw [Fintype.sum_eq_single p.1]
  · simp only [if_true]
    have := congrFun (sum_g_smul_xv B (fun a => M (posE n n' (p.1, a)).1 (posE n n' (p.1, a)).2)) p.2
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply] at this
    rw [this]
  · intro k hk
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (Ne.symm hk)]

theorem onB_bas : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.OnB D (bas B n n') := by
  intro D cc δ B n n'
  refine ⟨orthonormal_bas B n n', ?_⟩
  refine eq_top_iff.2 fun M _ => ?_
  rw [matrix_eq_sum_putB B n n' M]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨(ixE D n n').symm (k, w), ?_⟩
  simp [bas]

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficientStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_of_integrable_discreteSeries_coefficient : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  first | exact @GlobalTheory.CoefProjector.projector_of_integrable_coefficient | exact GlobalTheory.CoefProjector.projector_of_integrable_coefficient | (intros; apply GlobalTheory.CoefProjector.projector_of_integrable_coefficient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem pureLift_step : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  intro GM p hp R R₀ _ _ π hR hπ h2 g g' A B _ _ A₀ B₀ _ _ i j hA hgA hB hgB hi hj U V U₀ V₀ _ _ _ _ eU eV
    r s r' s' hU hV hu f₀ _ ef₀
  have h2' : RingHom.ker π ^ 2 = 0 := by rw [Ideal.zero_eq_bot]; exact h2
  obtain ⟨Hc, -, Hl⟩ := GM p hp R hR _ (GlobalTheory.Cris.divided₂ h2') (GlobalTheory.Cris.isDPNilpotent_squareZero h2') R₀ π hπ rfl
  set κ := GlobalTheory.Cris.divided₂ h2'
  have inj := (Hc.crysToDR_bijective hi hA hgA).1
  have key : ∀ d ∈ GlobalTheory.DeRham.liftFil κ hi, GlobalTheory.DeRham.push κ (spMap π) f₀ d ∈ GlobalTheory.DeRham.liftFil κ hj := by
    intro d hd
    have hd' : GlobalTheory.DeRham.crysToDR κ hi d ∈ GlobalTheory.DeRham.Fil A := hd
    have h1 : GlobalTheory.DeRham.push κ (spMap π) U₀ d = r • d := by
      apply inj
      rw [GlobalTheory.DeRham.crysToDR_push κ hi hi U₀ U eU, map_smul]
      exact hU.1 _ hd'
    have h3 : GlobalTheory.DeRham.push κ (spMap π) V₀ (GlobalTheory.DeRham.push κ (spMap π) f₀ d)
        = r • GlobalTheory.DeRham.push κ (spMap π) f₀ d := by
      have := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) U₀ f₀)
      have h4 := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) f₀ V₀)
      simp only [LinearMap.comp_apply] at this h4
      rw [← h4, ← GlobalTheory.DeRham.push_congr κ (spMap π) ef₀, this, h1, map_smul]
    show GlobalTheory.DeRham.crysToDR κ hj _ ∈ GlobalTheory.DeRham.Fil B
    refine IsPure.mem_Fil hV hu ?_
    rw [← GlobalTheory.DeRham.crysToDR_push κ hj hj V₀ V eV, h3, map_smul]
  obtain ⟨f, ⟨hf, ef⟩, uf⟩ := Hl g A₀ A i hi hA hgA g' B₀ B j hj hB hgB f₀ key
  refine ⟨f, hf, ef, ?_, fun f' hf' ef' => uf f' ⟨hf', ef'⟩⟩
  have e1 : i ≫ (U ≫ f).left = (U₀ ≫ f₀).left ≫ j := by
    simp only [Over.comp_left, ← Category.assoc, eU]
    simp only [Category.assoc, ef]
  have e2 : i ≫ (f ≫ V).left = (U₀ ≫ f₀).left ≫ j := by
    rw [Over.comp_left, ← Category.assoc, ef, Category.assoc, eV, ← Category.assoc, ← Over.comp_left, ← ef₀]
  exact Hl.unique hi hA hgA hj hB hgB (U₀ ≫ f₀) e1 e2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasisStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannian_volume_lie_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → IsOrth X x → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm X.Gm (e i *ᵥ u) w + herm X.Gm u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie X.Ψ e := by
  first | exact @GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | exact GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | (intros; apply GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinsetStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  first | exact @GlobalTheory.sections_coords_and_nonvanishing_at_finset | exact GlobalTheory.sections_coords_and_nonvanishing_at_finset | (intros; apply GlobalTheory.sections_coords_and_nonvanishing_at_finset <;> assumption)
end

