import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenformStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  first | exact @GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | exact GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | (intros; apply GlobalTheory.EigenSupport.inSupport_of_torus_eigenform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePair
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

namespace GlobalTheory.BadNoConj

theorem sall_noConj_ok : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr sel S mu hX hPr hsel u hT hg
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto
  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'

end GlobalTheory.BadNoConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverseStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_maximal_matrix_integral_inverse : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (X : Matrix (Fin n) (Fin n) L), (∀ i j, Valued.v (X i j) < 1) →
  ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧ ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.one_add_maximal_inv_int | exact GlobalTheory.Hk3.one_add_maximal_inv_int | (intros; apply GlobalTheory.Hk3.one_add_maximal_inv_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairMultMulRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelOps

variable {G : Type} [Group G]

def SameDC (K : Subgroup G) (a b : G) : Prop := ∃ k₁ ∈ K, ∃ k₂ ∈ K, b = k₁ * a * k₂

theorem SameDC.refl (K : Subgroup G) (a : G) : SameDC K a a :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem SameDC.symm {K : Subgroup G} {a b : G} (h : SameDC K a b) : SameDC K b a := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  exact ⟨k₁⁻¹, inv_mem h₁, k₂⁻¹, inv_mem h₂, by group⟩

theorem SameDC.trans {K : Subgroup G} {a b c : G} (h : SameDC K a b) (h' : SameDC K b c) : SameDC K a c := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  obtain ⟨l₁, i₁, l₂, i₂, rfl⟩ := h'
  exact ⟨l₁ * k₁, mul_mem i₁ h₁, k₂ * l₂, mul_mem h₂ i₂, by group⟩

theorem exists_dc_choice (K : Subgroup G) (a : G) :
    ∃ r : G → G, r a = a ∧ (∀ z, SameDC K z (r z)) ∧ ∀ b c, SameDC K b c → r b = r c := by
  classical
  let s : Setoid G := ⟨SameDC K, ⟨SameDC.refl K, SameDC.symm, SameDC.trans⟩⟩
  refine ⟨fun z => if SameDC K a z then a else (Quotient.mk s z).out, ?_, fun z => ?_, fun b c hbc => ?_⟩
  · simp [SameDC.refl K a]
  · by_cases hz : SameDC K a z
    · simpa [hz] using hz.symm
    · simp only [hz, if_false]
      exact SameDC.symm (Quotient.exact (s := s) (Quotient.out_eq (Quotient.mk s z)))
  · by_cases hb : SameDC K a b
    · simp [hb, hb.trans hbc]
    · have hc : ¬ SameDC K a c := fun h => hb (h.trans hbc.symm)
      simp only [hb, hc, if_false]
      rw [Quotient.sound (s := s) hbc]

theorem Reps.uniq {K : Subgroup G} {g a b c x : G} {R : Finset G} (h : Reps K g R) (ha : a ∈ R) (hb : b ∈ R)
    (e₁ : c⁻¹ * (x * a) ∈ K) (e₂ : c⁻¹ * (x * b) ∈ K) : a = b := by
  refine (h.2 b (h.1 b hb)).unique ⟨ha, ?_⟩ ⟨hb, by rw [inv_mul_cancel]; exact one_mem _⟩
  have := mul_mem (inv_mem e₁) e₂
  convert this using 1
  group

theorem Reps.exists_left {K : Subgroup G} {g γ k : G} {R R' : Finset G} (h : Reps K g R) (h' : Reps K g R')
    (hγ : γ ∈ R) (hk : k ∈ K) : ∃ δ ∈ R', δ⁻¹ * (k * γ) ∈ K := by
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h.1 γ hγ
  obtain ⟨δ, ⟨hδ, hd⟩, -⟩ := h'.2 (k * γ) ⟨k * k₁, mul_mem hk h₁, k₂, h₂, by rw [e]; group⟩
  exact ⟨δ, hδ, hd⟩

open Classical in

noncomputable def pairMult (K : Subgroup G) (R₁ R₂ : Finset G) (y : G) : ℕ :=
  ((R₁ ×ˢ R₂).filter fun p => (p.1 * p.2)⁻¹ * y ∈ K).card

theorem pairMult_le {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ y ≤ pairMult K R₁ R₂ (k * y) := by
  classical
  have ex1 : ∀ γ, γ ∈ R₁ → ∃ δ, δ ∈ R₁ ∧ δ⁻¹ * (k * γ) ∈ K := fun γ hγ =>
    (h₁.exists_left h₁ hγ hk).imp fun _ h => ⟨h.1, h.2⟩
  have ex2 : ∀ κ γ, κ ∈ K → γ ∈ R₂ → ∃ δ, δ ∈ R₂ ∧ δ⁻¹ * (κ * γ) ∈ K := fun κ γ hκ hγ =>
    (h₂.exists_left h₂ hγ hκ).imp fun _ h => ⟨h.1, h.2⟩
  choose! a ha using ex1
  choose! b hb using ex2
  unfold pairMult
  refine Finset.card_le_card_of_injOn (fun p => (a p.1, b ((a p.1)⁻¹ * (k * p.1)) p.2)) ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    have hκ := (ha _ p1).2
    have hb' := hb _ _ hκ p2
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(ha _ p1).1, hb'.1⟩, ?_⟩)
    have := mul_mem hb'.2 hp'.2
    convert this using 1
    simp only
    group
  · intro p hp q hq e
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    obtain ⟨q1, q2⟩ := Finset.mem_product.1 hq'.1
    have e1 : a p.1 = a q.1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e2
    have f1 : p.1 = q.1 := h₁.uniq p1 q1 (ha _ p1).2 (e1 ▸ (ha _ q1).2)
    rw [e1, f1] at e2
    have hκ := (ha _ q1).2
    have f2 : p.2 = q.2 := h₂.uniq p2 q2 (hb _ _ hκ p2).2 (e2 ▸ (hb _ _ hκ q2).2)
    exact Prod.ext f1 f2

theorem pairMult_mul_left {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ (k * y) = pairMult K R₁ R₂ y := by
  refine le_antisymm ?_ (pairMult_le h₁ h₂ hk y)
  simpa using pairMult_le h₁ h₂ (inv_mem hk) (k * y)

theorem pairMult_mul_right {K : Subgroup G} {k : G} (R₁ R₂ : Finset G) (hk : k ∈ K) (y : G) :
    pairMult K R₁ R₂ (y * k) = pairMult K R₁ R₂ y := by
  classical
  unfold pairMult
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [← mul_assoc, Subgroup.mul_mem_cancel_right _ hk]

theorem pairMult_dc {K : Subgroup G} {g h a b : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (e : SameDC K a b) : pairMult K R₁ R₂ b = pairMult K R₁ R₂ a := by
  obtain ⟨k₁, i₁, k₂, i₂, rfl⟩ := e
  rw [pairMult_mul_right _ _ i₂, pairMult_mul_left h₁ h₂ i₁]

open Classical in
theorem sum_single_of_dc {K : Subgroup G} {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y) {M : Type} [AddCommMonoid M] (F : G → M)
    (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) {z x₀ : G} (hx₀ : x₀ ∈ T) (hz : SameDC K x₀ z) :
    F z = ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * z ∈ K then F y else 0 := by
  obtain ⟨y₀, ⟨hy₀, e⟩, hu⟩ := (hS x₀ hx₀).2 z hz
  rw [Finset.sum_eq_single x₀ ?_ (fun h => absurd hx₀ h), Finset.sum_eq_single y₀ ?_ (fun h => absurd hy₀ h),
    if_pos e]
  · have := hF y₀ _ e
    rwa [mul_inv_cancel_left] at this
  · intro y hy hne
    exact if_neg fun h => hne (hu y ⟨hy, h⟩)
  · intro x hx hne
    refine Finset.sum_eq_zero fun y hy => if_neg fun h => hne ?_
    have hxy : SameDC K x y := (hS x hx).1 y hy
    have hyz : SameDC K y z := ⟨1, one_mem _, _, h, by group⟩
    exact hT x hx x₀ hx₀ ((hxy.trans hyz).trans hz.symm)

theorem sum_pairs_eq {K : Subgroup G} {g h : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y)
    (hcov : ∀ p ∈ R₁ ×ˢ R₂, ∃ x ∈ T, SameDC K x (p.1 * p.2))
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) :
    ∑ γ ∈ R₁, ∑ γ' ∈ R₂, F (γ * γ') = ∑ x ∈ T, pairMult K R₁ R₂ x • ∑ y ∈ S x, F y := by
  classical
  rw [← Finset.sum_product' (f := fun γ γ' => F (γ * γ'))]
  have e1 : ∀ p ∈ R₁ ×ˢ R₂, F (p.1 * p.2) =
      ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * (p.1 * p.2) ∈ K then F y else 0 := fun p hp => by
    obtain ⟨x, hx, hd⟩ := hcov p hp
    convert sum_single_of_dc hS hT F hF hx hd
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← Finset.sum_filter, Finset.sum_const, ← pairMult_dc h₁ h₂ ((hS x hx).1 y hy : SameDC K x y)]
  unfold pairMult
  congr 2
  refine Finset.filter_congr fun p _ => ?_
  have e : (p.1 * p.2)⁻¹ * y = (y⁻¹ * (p.1 * p.2))⁻¹ := by group
  rw [e, inv_mem_iff]

theorem reps_mul_decomp : ∀ {G : Type} [Group G] (K : Subgroup G) (g h : G) (R₁ R₂ : Finset G), GlobalTheory.SphLabelOps.Reps K g R₁ → GlobalTheory.SphLabelOps.Reps K h R₂ → ∃ (T : Finset G) (m : G → ℕ), g * h ∈ T ∧ (∀ x ∈ T, 0 < m x ∧ ∃ γ ∈ R₁, ∃ γ' ∈ R₂, ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * (γ * γ') * k₂) ∧ (∀ x ∈ T, ∀ y ∈ T, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → x = y) ∧ ∀ (S : G → Finset G), (∀ x ∈ T, GlobalTheory.SphLabelOps.Reps K x (S x)) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M), (∀ k ∈ K, π k u = u) → ∑ γ ∈ R₁, ∑ γ' ∈ R₂, π (γ * γ') u = ∑ x ∈ T, m x • ∑ y ∈ S x, π y u := by
  intro G _ K g h R₁ R₂ h₁ h₂
  classical
  obtain ⟨r, r0, r1, r2⟩ := exists_dc_choice K (g * h)
  have rr : ∀ z, r (r z) = r z := fun z => (r2 _ _ (r1 z)).symm
  have fixT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), r x = x := fun x hx => by
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    exact rr _
  have hT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)),
      ∀ y ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), SameDC K x y → x = y := fun x hx y hy e => by
    rw [← fixT x hx, ← fixT y hy]
    exact r2 _ _ e
  refine ⟨(R₁ ×ˢ R₂).image fun p => r (p.1 * p.2), pairMult K R₁ R₂, ?_, fun x hx => ?_, hT,
    fun S hS M _ _ π u hu => ?_⟩
  · obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h₁.2 g (SameDC.refl K g)
    obtain ⟨γ', ⟨hγ', e'⟩, -⟩ := h₂.2 (γ⁻¹ * g * h) ⟨_, e, 1, one_mem _, by group⟩
    refine Finset.mem_image.2 ⟨(γ, γ'), Finset.mem_product.2 ⟨hγ, hγ'⟩, ?_⟩
    have hd : SameDC K (γ * γ') (g * h) := ⟨1, one_mem _, _, e', by group⟩
    exact (r2 _ _ hd).trans r0
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    refine ⟨?_, p.1, p1, p.2, p2, r1 _⟩
    rw [pairMult_dc h₁ h₂ (r1 _)]
    refine Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩⟩
    rw [inv_mul_cancel]
    exact one_mem _
  · refine sum_pairs_eq h₁ h₂ hS hT (fun p hp => ⟨_, Finset.mem_image_of_mem _ hp, (r1 _).symm⟩)
      (fun z => π z u) fun x l hl => ?_
    rw [map_mul, Module.End.mul_apply, hu l hl]

end GlobalTheory.SphLabelOps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  first | exact @GlobalTheory.SmGL.BlockRename.multiProd_rename | exact GlobalTheory.SmGL.BlockRename.multiProd_rename | (intros; apply GlobalTheory.SmGL.BlockRename.multiProd_rename <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α'] [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)] (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)), Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  first | exact @GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | exact GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | (intros; apply GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLocalEigen_galoisPolynomial_split : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalEig.main | exact GlobalTheory.PtLocalEig.main | (intros; apply GlobalTheory.PtLocalEig.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem intOff_finset_prod {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IntOff.one : IntOff S 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem xiCpl1_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ al p₀ p Yb x
  have hm : t.m2 < D.R.m := by have := (t.idx_ok μ).hm; omega
  unfold XiCpl1
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · rw [map_one]; exact IntOff.one
    · rw [map_zero]; exact IntOff.zero
  · unfold PsiAt
    first
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumTemperedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_sum_tempered : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  first | exact @GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | exact GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | (intros; apply GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLatticeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_one_add_skewHermitian_mul_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  first | exact @GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | exact GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | (intros; apply GlobalTheory.SelfDualUnip.selfDual_mul_of_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentityStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  first | exact @GlobalTheory.skewConj_cT_mul_and_trace | exact GlobalTheory.skewConj_cT_mul_and_trace | (intros; apply GlobalTheory.skewConj_cT_mul_and_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelComm

section Abstract

variable {G : Type} [Group G]

theorem isDC_of_reps {K : Subgroup G} {x : G} {A : Finset G} (h : GlobalTheory.SphLabelOps.Reps K x A) :
    Formalism.IndefR.Bridge.IsDC K x A := by
  refine ⟨fun a ha => ?_, fun g hg => h.2 g ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hg
    exact ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩

theorem sum_comm_of_antiInv (K L : Subgroup G) (hKL : K ≤ L) (θ : G → G)
    (t1 : ∀ g ∈ L, θ g ∈ L) (t2 : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (t3 : ∀ x ∈ L, θ (θ x) = x)
    (t4 : ∀ k ∈ K, θ k ∈ K) (t5 : ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) {A B A' : Finset G}
    (hA : GlobalTheory.SphLabelOps.Reps K x A) (hB : GlobalTheory.SphLabelOps.Reps K y B) (hA' : GlobalTheory.SphLabelOps.Reps K x⁻¹ A')
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u) :
    ∑ a ∈ A, π a (∑ b ∈ B, π b u) = ∑ b ∈ B, π b (∑ a ∈ A, π a u) := by
  have memL : ∀ {z : G} {R : Finset G}, GlobalTheory.SphLabelOps.Reps K z R → z ∈ L → ∀ a ∈ R, a ∈ L := by
    intro z R hR hz a ha
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR.1 a ha
    exact mul_mem (mul_mem (hKL h₁) hz) (hKL h₂)
  have hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧
      (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K ⊓ L, θ k ∈ K) ∧ ∀ g ∈ L, ∃ a ∈ K ⊓ L, ∃ b ∈ K ⊓ L, θ g = a * g * b := by
    refine ⟨θ, t1, t2, t3, fun k hk => t4 k hk.1, fun g hg => ?_⟩
    obtain ⟨a, ha, b, hb, e⟩ := t5 g hg
    exact ⟨a, ⟨ha, hKL ha⟩, b, ⟨hb, hKL hb⟩, e⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hF : ∀ (k : K) (h : G), (fun g => φ (π g u)) (h * k) = ((1 : K →* ℂˣ) k : ℂ) • (fun g => φ (π g u)) h := by
    intro k h
    simp [map_mul, Module.End.mul_apply, hu k k.2]
  have key := (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) K L 1 x y A B A' (fun g => φ (π g u))
    (fun k hk => ⟨k, hk, 1, one_mem _, hKL hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun k _ => rfl) hθ (memL hA hx) (memL hB hy) (memL hA' (inv_mem hx)) (isDC_of_reps hA) (isDC_of_reps hB)
    (isDC_of_reps hA') hF).1
  have e := congrFun key 1
  simp only [Formalism.IndefR.Bridge.dcOp, one_mul, map_mul, Module.End.mul_apply] at e
  simp only [map_sub, map_sum, LinearMap.zero_apply]
  rw [sub_eq_zero]
  exact e

theorem comb_comm {ι M : Type} [AddCommGroup M] [Module ℂ M] (S : ι → Module.End ℂ M) (u : M)
    (h : ∀ i j, S i (S j u) = S j (S i u)) (c c' : ι →₀ ℂ) :
    (c.sum fun i z => z • S i) ((c'.sum fun i z => z • S i) u) =
      (c'.sum fun i z => z • S i) ((c.sum fun i z => z • S i) u) := by
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j, smul_comm]

end Abstract

open GlobalTheory.IdemSupport in

theorem label_ops_comm : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  intro D V P c c' M _ _ π u hu
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  have memK : ∀ k, k ∈ K ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := fun k => by
    rw [← SetLike.mem_coe, ← hK, GlobalTheory.SphLabelOps.hyp_eq h]
    rfl
  have hKL : K ≤ L := fun k hk => (hL k).2 ((memK k).1 hk).2
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ : ∃ θ : GA D V → GA D V, (∀ g ∈ L, θ g ∈ L) ∧
      (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K, θ k ∈ K) ∧
      ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨θ, s1, s2, s3, s4, s5⟩ := (GlobalTheory.SplitPlace.split_local V P e hs).1
      refine ⟨θ, fun g hg => (hL _).2 (s1 g ((hL g).1 hg)), fun x hx y hy => s2 x y ((hL x).1 hx) ((hL y).1 hy),
        fun x hx => s3 x ((hL x).1 hx), fun k hk => ?_, fun g hg => ?_⟩
      · have hk' := (memK k).1 hk
        exact (memK _).2 ⟨s4 k hk', s1 k hk'.2⟩
      · obtain ⟨a, ha, b, hb, eq⟩ := s5 g ((hL g).1 hg)
        exact ⟨a, (memK a).2 ha, b, (memK b).2 hb, eq⟩
    · refine ⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
        fun k hk => inv_mem hk, fun g hg => ?_⟩
      obtain ⟨a, b, ha, ha', hb, hb', eq⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ h
        (GlobalTheory.SphLabelOps.exists_real_unif D P) g ((hL g).1 hg)).1
      exact ⟨a, (memK a).2 ⟨ha, ha'⟩, b, (memK b).2 ⟨hb, hb'⟩, eq⟩
  have reps : ∀ d, IsLab V P d → ∃ x ∈ L, GlobalTheory.SphLabelOps.Reps K x (rep V P d) ∧
      ∃ A', GlobalTheory.SphLabelOps.Reps K x⁻¹ A' := by
    intro d hd
    have hR := GlobalTheory.SphLabelOps.sphOp_rep hd
    obtain ⟨e', f', ϖ, α, -, h', h1, h2, -, -, -, hα, hD, -⟩ := id hR
    obtain ⟨rfl, rfl⟩ := h0.2.2.2.1 e' f' h'
    have hαL : α ∈ L := (hL α).2 hα
    refine ⟨α, hαL, GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 hα hD hR, ?_⟩
    obtain ⟨R', hR', -⟩ := GlobalTheory.SphLabelOps.exists_dual hR
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h').1
    exact ⟨R', GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 ((hL _).1 (inv_mem hαL))
      (GlobalTheory.DivDual.divAt_inv_and_mul V _ _ d α he (GlobalTheory.SphLabelOps.unif_ne_zero h2) hD).1 hR'⟩
  have key : ∀ d d', (∑ γ ∈ rep V P d, π γ) ((∑ δ ∈ rep V P d', π δ) u) =
      (∑ δ ∈ rep V P d', π δ) ((∑ γ ∈ rep V P d, π γ) u) := by
    intro d d'
    by_cases hd : IsLab V P d
    swap
    · simp [Hk3.rep, dif_neg hd]
    by_cases hd' : IsLab V P d'
    swap
    · simp [Hk3.rep, dif_neg hd']
    obtain ⟨x, hx, rA, A', rA'⟩ := reps d hd
    obtain ⟨y, hy, rB, -⟩ := reps d' hd'
    simp only [LinearMap.sum_apply]
    exact sum_comm_of_antiInv K L hKL θ t1 t2 t3 t4 t5 hx hy rA rB rA' π u
      (fun k hk => hu k (by rw [hK]; exact hk))
  exact comb_comm (fun d => ∑ γ ∈ rep V P d, π γ) u key c c'

end GlobalTheory.SphLabelComm
end

