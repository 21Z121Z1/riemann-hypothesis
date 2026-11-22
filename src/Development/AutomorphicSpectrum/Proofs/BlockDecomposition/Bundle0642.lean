import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0004
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SphLine

section Abstract

open GlobalTheory.LFun GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem finrank_fixed_eq_one (π : Representation ℂ G V) (K : Subgroup G) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hfd : FiniteDimensional ℂ (fixed π K)) (hne : fixed π K ≠ ⊥) :
    Module.finrank ℂ (fixed π K) = 1 := by
  obtain ⟨x₀, hx₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have key : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x₀) = c • x₀ := fun g => by
    obtain ⟨N, hN, e⟩ := HeckeScalar.heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    obtain ⟨c, hc'⟩ := HeckeScalar.exists_scalar G V π K hc hK hcomm hπ hfd _ (Final.DosetIndMem G K ℂ g)
    have h1 := hc' x₀ hx₀
    rw [e] at h1
    refine ⟨N⁻¹ * c, ?_⟩
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have all : ∀ a : MonoidAlgebra ℂ G, ∃ c : ℂ, idem hπ.1 hc (orbitMap π x₀ a) = c • x₀ := fun a => by
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      obtain ⟨c, hc₁⟩ := ha
      obtain ⟨d, hd⟩ := hb
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      exact ⟨c + d, by rw [this, map_add, hc₁, hd, add_smul]⟩
    | smul r a ha =>
      obtain ⟨c, hc₁⟩ := ha
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      exact ⟨r * c, by rw [this, map_smul, hc₁, smul_smul]⟩
  refine (finrank_eq_one_iff_of_nonzero' (⟨x₀, hx₀⟩ : fixed π K) fun e => h0 (congrArg Subtype.val e)).2 ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := orbitMap_surjective hπ.2 h0 x
  obtain ⟨c, hc₁⟩ := all a
  refine ⟨c, Subtype.ext ?_⟩
  rw [ha, idem_of_mem hπ.1 hc hx] at hc₁
  exact hc₁.symm

end Abstract

section Gelfand

theorem conv_comm_sub {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K)
    (hdc : ∀ g : H, ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b)
    (f₁ f₂ : H → ℂ) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : conv K f₁ f₂ = conv K f₂ f₁ :=
  Formalism.UG.P.heckecomm_gelfand K (fun x : H => (⟨θ x, hH _ x.2⟩ : H)) (fun x y => Subtype.ext (hm _ _))
    (fun x => Subtype.ext (hi _)) hK hdc f₁ f₂ hf₁ hf₂

theorem dc_of_decomp {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K) {g k₁ k₂ t : H} (h₁ : k₁ ∈ K) (h₂ : k₂ ∈ K)
    (ht : θ t = t) (e : g = k₁ * t * k₂) : ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b := by
  have hm' : ∀ x y : H, (⟨θ (x * y : H), hH _ (x * y).2⟩ : H) = ⟨θ y, hH _ y.2⟩ * ⟨θ x, hH _ x.2⟩ :=
    fun x y => Subtype.ext (hm _ _)
  have ht' : (⟨θ t, hH _ t.2⟩ : H) = t := Subtype.ext ht
  refine ⟨⟨_, K.mul_mem (hK _ h₂) (K.inv_mem h₁)⟩, ⟨_, K.mul_mem (K.inv_mem h₂) (hK _ h₁)⟩, ?_⟩
  subst e
  simp only [hm', ht']
  group

end Gelfand

section Transpose

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem tr_mem_UJ (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {h : GL (Fin n) L} (hh : h ∈ UJ σ (antiJ L n)) :
    Formalism.UG.P.heckecomm_tr h ∈ UJ σ (antiJ L n) := by
  have hJ : antiJ L n * antiJ L n = 1 := GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJσ : (antiJ L n).map σ = antiJ L n := by
    ext i j
    simp only [Matrix.map_apply, antiJ]
    split_ifs <;> simp
  have h0 : cT σ h.val * antiJ L n * h.val = antiJ L n := hh
  have hmm : ((h.val.map σ)ᵀ).map σ = h.valᵀ := by
    ext i j
    simp [hσ]
  have h1 : h.valᵀ * antiJ L n * h.val.map σ = antiJ L n := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => M.map σ) h0
    simp only [cT, Matrix.map_mul, hJσ, hmm] at this
    exact this
  have h2 : h.valᵀ * (antiJ L n * h.val.map σ * antiJ L n) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, hJ]
  have h3 : (antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ = 1 := mul_eq_one_comm.1 h2
  change cT σ (Formalism.UG.P.heckecomm_tr h).val * antiJ L n * (Formalism.UG.P.heckecomm_tr h).val = antiJ L n
  have hc : cT σ (Formalism.UG.P.heckecomm_tr h).val = h.val.map σ := by
    ext i j
    simp [cT, Formalism.UG.P.heckecomm_tr_val]
  rw [hc, Formalism.UG.P.heckecomm_tr_val]
  calc h.val.map σ * antiJ L n * h.valᵀ
      = antiJ L n * ((antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ) := by
        simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    _ = antiJ L n := by rw [h3, Matrix.mul_one]

def thb (b x : GL (Fin n) L) : GL (Fin n) L := b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹

theorem thb_mul (b x y : GL (Fin n) L) : thb b (x * y) = thb b y * thb b x := by
  unfold thb
  rw [show b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) by group, Formalism.UG.P.heckecomm_tr_mul]
  group

theorem thb_thb (b x : GL (Fin n) L) : thb b (thb b x) = x := by
  unfold thb
  rw [show b⁻¹ * (b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹) * b = Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) by group,
    Formalism.UG.P.heckecomm_tr_tr]
  group

end Transpose

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  by_cases hw : IsSplitAt w
  · have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact isClosed_univ
  · rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

theorem coe_KL (n : ℕ) (w : Pl E) :
    (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  ext x
  exact Subgroup.mem_subgroupOf

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage continuous_subtype_val

theorem isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) : IsCompact (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2

theorem conv_comm_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  have hT : UL n w = ⊤ := if_pos hw
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    rw [hT]
    trivial
  refine conv_comm_sub (UL n w) (KL n w) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x _ => hmem _) (fun x hx => ?_) (fun g => ?_) f₁ f₂ hf₁ hf₂
  · exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ (Subgroup.mem_subgroupOf.1 hx))
  · obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨⟨a.1, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2⟩, ⟨⟨b.1, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2⟩,
      Subtype.ext e⟩

theorem conv_comm_inert (hU : Unr E) {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  obtain ⟨-, hcc, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ _ n) := fun g => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b g hb'
  have hback : ∀ x ∈ UL n w, b⁻¹ * x * b ∈ UJ (cj w) (antiJ _ n) := fun x hx =>
    (hconj _).1 (by rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group])
  have hH : ∀ x ∈ UL n w, thb b x ∈ UL n w := fun x hx =>
    (hconj _).2 (tr_mem_UJ _ hcc (hback x hx))
  have hbi := (GlobalTheory.LFun.KGL w n).inv_mem hbK
  have hK : ∀ x : UL n w, x ∈ KL n w → (⟨thb b x, hH _ x.2⟩ : UL n w) ∈ KL n w := fun x hx =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _
      (mul_mem (mul_mem hbi (Subgroup.mem_subgroupOf.1 hx)) hbK))) hbi)
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  refine conv_comm_sub (UL n w) (KL n w) (thb b) (thb_mul b) (thb_thb b) hH hK (fun g => ?_) f₁ f₂ hf₁ hf₂
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback g.1 g.2⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hk : ∀ k ∈ KU (cj w) n, (⟨b * k.1 * b⁻¹, (hconj _).2 k.2⟩ : UL n w) ∈ KL n w := fun k hk =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (hKU k hk)) hbi)
  refine dc_of_decomp (UL n w) (KL n w) (thb b) (thb_mul b) hH hK (hk k₁ hk₁) (hk k₂ hk₂)
    (t := ⟨b * t.1 * b⁻¹, (hconj _).2 t.2⟩) ?_ (Subtype.ext ?_)
  · have h1 : Formalism.UG.P.heckecomm_tr (t.1 : GLw n w) = t.1 := Units.ext (by
      rw [Formalism.UG.P.heckecomm_tr_val, ht]
      exact Matrix.diagonal_transpose _)
    show thb b (b * t.1 * b⁻¹) = b * t.1 * b⁻¹
    unfold thb
    rw [show b⁻¹ * (b * t.1 * b⁻¹) * b = t.1 by group, h1]
  · show g.1 = b * k₁.1 * b⁻¹ * (b * t.1 * b⁻¹) * (b * k₂.1 * b⁻¹)
    calc g.1 = b * (b⁻¹ * g.1 * b) * b⁻¹ := by group
      _ = _ := by
        rw [e']
        group

theorem sphOne : SphOne := by
  intro E _ _ _ hU n w σ hne hfd
  have hcomm : ∀ f₁ ∈ Hecke ℂ (KL n w), ∀ f₂ ∈ Hecke ℂ (KL n w),
      conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := fun f₁ h₁ f₂ h₂ => by
    by_cases hw : IsSplitAt w
    · exact conv_comm_split hw f₁ f₂ h₁.1 h₂.1
    · exact conv_comm_inert hU hw f₁ f₂ h₁.1 h₂.1
  exact finrank_fixed_eq_one σ.ρ (KL n w) (isCompact_KL hU n w)
    (PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ (isOpen_KL n w) (isCompact_KL hU n w)) hcomm
    ⟨σ.smooth, σ.irred⟩ hfd hne

theorem locAlg_sphOne : LocAlg → SphOne := fun _ => sphOne

end Local

end GlobalTheory.CompanionTheory.SphLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisM

section Abstract

variable {X H : Type}

def TestAlg [TopologicalSpace X] (A : Submodule ℂ (X → ℂ)) : Prop :=
  (∀ f ∈ A, Continuous f ∧ HasCompactSupport f) ∧ (∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) ∧ (∀ f ∈ A, star f ∈ A) ∧
    (∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) ∧
    ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1

def InJ [MeasurableSpace X] [MeasurableSpace H] (lam : Measure H) (Q : Measure X) (p : H → X → ℂ) (ξ : X → ℂ) : Prop :=
  Integrable ξ Q ∧ Integrable (fun x => ∫ z, ξ z * p x z ∂Q) lam

def LJ [MeasurableSpace X] [MeasurableSpace H] (lam : Measure H) (Q : Measure X) (p : H → X → ℂ) (ξ : X → ℂ) : ℂ :=
  ∫ x, ∫ z, ξ z * p x z ∂Q ∂lam

end Abstract

variable {D : D7} {N r t n : ℕ}

abbrev XS (e : AE D) (N r t : ℕ) : Type := {z : Mx D N r × Mx D N t // e • z.1 = z.1 ∧ e • z.2 = z.2}

def testA (θ : InfFam D) (S : Finset (Pl D)) (e : AE D) (hn : r + t = n) : Submodule ℂ (XS e N r t → ℂ) where
  carrier := {f | ∃ Φ ∈ schwartzA θ N n, Good S e Φ ∧ HasCompactSupport Φ ∧ ∀ z : XS e N r t, f z = Φ (jn hn z.1.1 z.1.2)}
  add_mem' := by
    rintro f f' ⟨Φ, h₁, h₂, h₃, h₄⟩ ⟨Φ', h₁', h₂', h₃', h₄'⟩
    refine ⟨Φ + Φ', Submodule.add_mem _ h₁ h₁', fun x => ?_, h₃.add h₃', fun z => ?_⟩
    · have a := h₂ x
      have b := h₂' x
      by_cases h : IntOff S x
      · simp only [Pi.add_apply, if_pos h] at a b ⊢
        rw [a, b]
      · simp only [Pi.add_apply, if_neg h] at a b ⊢
        rw [a, b, add_zero]
    · simp only [Pi.add_apply, h₄, h₄']
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, HasCompactSupport.zero, fun z => rfl⟩
    simp
  smul_mem' := by
    rintro c f ⟨Φ, h₁, h₂, h₃, h₄⟩
    refine ⟨c • Φ, Submodule.smul_mem _ c h₁, fun x => ?_, h₃.smul_left, fun z => ?_⟩
    · have a := h₂ x
      by_cases h : IntOff S x
      · simp only [Pi.smul_apply, if_pos h] at a ⊢
        rw [a]
      · simp only [Pi.smul_apply, if_neg h] at a ⊢
        rw [a, smul_zero]
    · simp only [Pi.smul_apply, h₄]

def toXS {e : AE D} (he : e * e = e) (z : Mx D N r × Mx D N t) : XS e N r t :=
  ⟨(e • z.1, e • z.2), by simp only [smul_smul, he, and_self]⟩

def PS {e : AE D} (he : e * e = e) (S : Finset (Pl D)) (P : Measure (Mx D N r × Mx D N t)) : Measure (XS e N r t) :=
  (P.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map (toXS he)

def pk (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (b₀ : HermE D r) {e : AE D} (x : hermS D t e) (z : XS e V.rank r t) : ℂ :=
  pch ψ x.1.1 (qv V b₀ z.1)

def xi (V : HSp D) (b₀ : HermE D r) (hn : r + t = n) {e : AE D} (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ)
    (z : XS e V.rank r t) : ℂ :=
  Φ (jn hn z.1.1 z.1.2) * conj (η (yv V b₀ z.1))

def phiU (V : HSp D) (r t : ℕ) (h : GA D V) : (Mx D V.rank r × Mx D V.rank t) ≃ₜ (Mx D V.rank r × Mx D V.rank t) where
  toFun z := (mm (mt V h) z.1, mm (mt V h) z.2)
  invFun z := (mm (mt V h⁻¹) z.1, mm (mt V h⁻¹) z.2)
  left_inv z := by
    have e₁ : mt V h⁻¹ * mt V h = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h⁻¹ * (mt V h * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h⁻¹ * (mt V h * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  right_inv z := by
    have e₁ : mt V h * mt V h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h * (mt V h⁻¹ * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h * (mt V h⁻¹ * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)
  continuous_invFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)

def phiS (N : ℕ) (y : Mx D r t) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, z.2 + mm z.1 y)
  invFun z := (z.1, z.2 + mm z.1 (-y))
  left_inv z := by simp [Matrix.mul_neg]
  right_inv z := by simp [Matrix.mul_neg]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))

def phiG (N r : ℕ) (g : GL (Fin t) (AE D)) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, mm z.2 g.1)
  invFun z := (z.1, mm z.2 (g⁻¹).1)
  left_inv z := by
    have e₁ : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * g.1 : Matrix _ _ _) * (g⁻¹).1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  right_inv z := by
    have e₁ : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * (g⁻¹).1 : Matrix _ _ _) * g.1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

def tauG {e : AE D} (g : GL (Fin t) (AE D)) (x : hermS D t e) : hermS D t e :=
  ⟨⟨mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1), by
      have hx : adj x.1.1 = x.1.1 := x.1.2
      change adj (mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1)) = _
      simp only [mm, adj_mul, adj_adj, hx]
      rw [Matrix.mul_assoc]⟩, by
      have hx : e • x.1.1 = x.1.1 := x.2
      change e • (mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1)) = _
      simp only [mm]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hx]⟩

end GlobalTheory.CompanionTheory.EisM

namespace GlobalTheory.CompanionTheory.EisM
variable {D : D7} {N r t n : ℕ}

def liftU {e : AE D} (V : HSp D) (r t : ℕ) (h : GA D V) : XS e V.rank r t ≃ₜ XS e V.rank r t :=
  (phiU V r t h).subtype (fun z => by
    have a : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) (e • x) := fun x => (Matrix.mul_smul _ _ _).symm
    have b : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) x → e • x = x := fun {k} x hx => by
      have i := congrArg (fun y => mm (mt V h⁻¹) y) hx
      have l : ∀ y : Mx D V.rank k, mm (mt V h⁻¹) (mm (mt V h) y) = y := fun y =>
        congrArg Prod.fst ((phiU V k k h).left_inv (y, y))
      simpa only [a, l] using i
    refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨b _ hz.1, b _ hz.2⟩⟩
    · change e • mm (mt V h) z.1 = mm (mt V h) z.1
      rw [a, hz.1]
    · change e • mm (mt V h) z.2 = mm (mt V h) z.2
      rw [a, hz.2])

def liftS {e : AE D} (N : ℕ) (y : Mx D r t) : XS e N r t ≃ₜ XS e N r t :=
  (phiS N y).subtype (fun z => by
    have a : ∀ x : Mx D N r, e • x = x → e • mm x y = mm x y := fun x hx => by
      simp only [mm]
      rw [← Matrix.smul_mul, hx]
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • (z.2 + mm z.1 y) = z.2 + mm z.1 y
      rw [smul_add, hz.2, a _ hz.1]
    · have h₂ : e • (z.2 + mm z.1 y) = z.2 + mm z.1 y := hz.2
      have h₁ : e • z.1 = z.1 := hz.1
      rw [smul_add, a _ h₁] at h₂
      exact add_right_cancel h₂)

def liftG {e : AE D} (N r : ℕ) (g : GL (Fin t) (AE D)) : XS e N r t ≃ₜ XS e N r t :=
  (phiG N r g).subtype (fun z => by
    have a : ∀ x : Mx D N t, e • mm x g.1 = mm (e • x) g.1 := fun x => (Matrix.smul_mul _ _ _).symm
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • mm z.2 g.1 = mm z.2 g.1
      rw [a, hz.2]
    · have h₂ : e • mm z.2 g.1 = mm z.2 g.1 := hz.2
      have i := congrArg (fun y => mm y (g⁻¹).1) h₂
      have l : ∀ y : Mx D N t, mm (mm y g.1) (g⁻¹).1 = y := fun y =>
        congrArg Prod.snd ((phiG N r g).left_inv ((0 : Mx D N r), y))
      simpa only [a, l] using i)

end GlobalTheory.CompanionTheory.EisM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubreps
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.WhitSup

theorem mem_sup_of_mem_twKer_sup {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (X Y : Subrepresentation ρ) (H : Subgroup G) (χ : H →* ℂˣ)
    {w : (X ⊔ Y).toSubmodule} (hw : w ∈ twKer (X ⊔ Y).toRepresentation H χ) :
    (w : V) ∈ X.toSubmodule ⊓ twKer ρ H χ ⊔ Y.toSubmodule ⊓ twKer ρ H χ := by
  unfold GlobalTheory.PRep.twKer at hw ⊢
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, u, rfl⟩ := hz
    have hu : (u : V) ∈ X.toSubmodule ⊔ Y.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup]
      exact u.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hu
    have hρu : ((X ⊔ Y).toRepresentation h u : V) = ρ h u := rfl
    have hcoe : (((X ⊔ Y).toRepresentation h u - (χ h : ℂ) • u : (X ⊔ Y).toSubmodule) : V) =
        (ρ h x - (χ h : ℂ) • x) + (ρ h y - (χ h : ℂ) • y) := by
      rw [Submodule.coe_sub, Submodule.coe_smul, hρu, ← hxy, map_add, smul_add]
      abel
    rw [hcoe]
    apply Submodule.add_mem_sup
    · exact Submodule.mem_inf.2
        ⟨X.toSubmodule.sub_mem (X.apply_mem_toSubmodule h hx) (X.toSubmodule.smul_mem _ hx),
          Submodule.subset_span ⟨h, x, rfl⟩⟩
    · exact Submodule.mem_inf.2
        ⟨Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule h hy) (Y.toSubmodule.smul_mem _ hy),
          Submodule.subset_span ⟨h, y, rfl⟩⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ c ha

theorem sup_inf_twKer_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ X Y w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
  have hW : GlobalTheory.PRep.IsSmooth (X ⊔ Y).toRepresentation := by
    unfold GlobalTheory.PRep.IsSmooth at hρ ⊢
    intro v
    have hset : {g | (X ⊔ Y).toRepresentation g v = v} = {g | ρ g v = v} := by
      ext g
      exact Subtype.ext_iff
    rw [hset]
    exact hρ v
  have hw' : (⟨w, hw1⟩ : (X ⊔ Y).toSubmodule) ∈ GlobalTheory.PRep.twKer
      (X ⊔ Y).toRepresentation (GlobalTheory.SmGL.unipB k (Fin N))
      (GlobalTheory.LocGL.whitChar ψ N) :=
    GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N (X ⊔ Y).toRepresentation ρ
      hW hρ (X ⊔ Y).toSubmodule.subtype Subtype.val_injective (fun _ _ => rfl) _ hw2
  exact GlobalTheory.CompanionTheory.PRep.WhitSup.mem_sup_of_mem_twKer_sup X Y _ _ hw'

end GlobalTheory.CompanionTheory.PRep.WhitSup

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerPureTensorFormulaStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_pure_tensor_formula : Ad3.SchwartzSpaceL2.SPure := by
  first | exact @GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt | exact GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt | (intros; apply GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslationStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_right_translation : Ad3.SchwartzSpaceL2.STrans := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | exact GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | (intros; apply GlobalTheory.CompanionTheory.WhittakerTrans.sTrans <;> assumption)
end

