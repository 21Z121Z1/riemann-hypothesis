import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulApplyZero
section
open GlobalTheory.WeilM

noncomputable section

open scoped Classical Topology

namespace GlobalTheory.CharForm

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def cosetInd (U : AddSubgroup X) (q : X ⧸ U) : X → ℂ := fun x => if (x : X ⧸ U) = q then 1 else 0

theorem cosetInd_mem_SB (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X)) (q : X ⧸ U) :
    cosetInd U q ∈ SB X := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  refine ⟨?_, ?_⟩
  · exact (IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous
      QuotientAddGroup.continuous_mk
  · have hK : IsCompact ((fun u => q.out + u) '' (U : Set X)) := hUc.image (continuous_const.add continuous_id)
    have hKc : IsClosed ((fun u => q.out + u) '' (U : Set X)) :=
      (Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)
    refine HasCompactSupport.intro' hK hKc fun x hx => ?_
    simp only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hxq
    apply hx
    refine ⟨-q.out + x, ?_, by simp⟩
    rw [← QuotientAddGroup.out_eq' q] at hxq
    exact QuotientAddGroup.eq.mp hxq.symm

theorem exists_periodic {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose W hWo _ hWN _ using fun x => H _ (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ =>
    ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  have hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X) :=
    Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)
  obtain ⟨U, hUo, hUc, hUN, hUk⟩ := H _ hNm
  refine ⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ W x := Set.mem_iInter₂.mp (hUN hu).2 x hxt
    have h1 : g (x + (y - x)) = g x := hWN x hyx
    have h2 : g (x + (y - x + u)) = g x := hWN x ((W x).add_mem hyx hu')
    rw [add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

theorem apply_eq_of_periodic {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ x : X, g ((x : X ⧸ U).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]; exact hper x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • cosetInd U q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))
  have hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0 := by
    intro q hq
    have hx₀ : q.out ∉ U := by
      intro hm
      apply hq
      rw [← QuotientAddGroup.out_eq' q]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hm
    obtain ⟨χ, hχC, hχU, hχ1⟩ := hUk _ hx₀
    have hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q := by
      funext x
      simp only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs with hxq
      · have hm : -q.out + x ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hxq
          exact QuotientAddGroup.eq.mp hxq.symm
        have := hχU _ hm
        rwa [add_neg_cancel_left] at this
      · rfl
    have e := ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)
    rw [hmul, map_smul, smul_eq_mul] at e
    have : (χ q.out - 1) * a (cosetInd U q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_eq_single (0 : X ⧸ U)]
  · rw [map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]
  · intro q _ hq
    rw [map_smul, hkill q hq, smul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self _ _) h

theorem exists_eq_mul_apply_zero : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (C : Set (X → ℂ)),
    (∀ N ∈ nhds (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) →
    ∀ (a : (X → ℂ) →ₗ[ℂ] ℂ), (∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g) →
      ∃ c : ℂ, ∀ g ∈ SB X, a g = c * g 0 := by
  intro X _ _ _ C H a ha
  obtain ⟨U₀, hU₀o, hU₀c, -, hU₀k⟩ := H Set.univ Filter.univ_mem
  refine ⟨a (cosetInd U₀ 0), fun g hg => ?_⟩
  obtain ⟨U, hUo, hUc, hUV, hUk, hper⟩ := exists_periodic H hg (hU₀o.mem_nhds U₀.zero_mem)
  have h1 := apply_eq_of_periodic a ha U hUo hUc hUk hg hper
  have h2 := apply_eq_of_periodic a ha U hUo hUc hUk (cosetInd_mem_SB U₀ hU₀o hU₀c 0) fun x u hu => by
    have : ((u : X) : X ⧸ U₀) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr (hUV hu)
    simp only [cosetInd, QuotientAddGroup.mk_add, this, add_zero]
  have h0 : cosetInd U₀ (0 : X ⧸ U₀) 0 = 1 := by simp [cosetInd]
  rw [h0, one_mul] at h2
  rw [h1, h2, mul_comm]

end GlobalTheory.CharForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticeClassesFibreSummand
section
open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_eq_one_of_mul {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (by rw [h, one_mul])
  apply Units.ext
  apply RingOfIntegers.coe_injective
  simp [h1]

def pairOf {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) : LatPair 𝔞 𝔟 :=
  ⟨((x.2 : F), rep x.1), x.2.2, rep_mem x.1, fun h => rep_ne_zero x.1 (congrArg Prod.snd h)⟩

theorem out_mk {𝔞 𝔟 : Frac F} (p : LatPair 𝔞 𝔟) :
    ∃ ε : (𝓞 F)ˣ, (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧
      (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = ((ε : 𝓞 F) : F) * p.1.2 :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (latRel 𝔞 𝔟) p)).symm

private lemma ringOfIntegers_unit_coe_ne_zero (ε : (𝓞 F)ˣ) : ((ε : 𝓞 F) : F) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (unit_inv_mul ε)

theorem out_mk_ne {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    (Quotient.mk (latRel 𝔞 𝔟) (pairOf x)).out.1.2 ≠ 0 := by
  obtain ⟨ε, -, h2⟩ := out_mk (pairOf x)
  rw [h2]
  exact mul_ne_zero (ringOfIntegers_unit_coe_ne_zero ε) (rep_ne_zero x.1)

def fibreMap (𝔞 𝔟 : Frac F) (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} :=
  ⟨Quotient.mk _ (pairOf x), out_mk_ne x⟩

theorem fibreMap_injective (𝔞 𝔟 : Frac F) : Function.Injective (fibreMap 𝔞 𝔟) := by
  rintro ⟨β, a⟩ ⟨β', a'⟩ h
  have h' : Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β, a⟩) = Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β', a'⟩) :=
    congrArg Subtype.val h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h'
  have hβ : β = β' :=
    (Quotient.out_eq (s := unitRel 𝔟) β).symm.trans
      ((Quotient.sound (s := unitRel 𝔟) (a := Quotient.out (s := unitRel 𝔟) β)
        (b := Quotient.out (s := unitRel 𝔟) β') ⟨ε, h2⟩).trans (Quotient.out_eq (s := unitRel 𝔟) β'))
  subst hβ
  have hε : ε = 1 := unit_eq_one_of_mul (rep_ne_zero β) h2.symm
  subst hε
  have haa : a = a' := Subtype.ext (by simpa [pairOf] using h1.symm)
  subst haa
  rfl

theorem fibreMap_surjective (𝔞 𝔟 : Frac F) : Function.Surjective (fibreMap 𝔞 𝔟) := by
  rintro ⟨c, hc⟩
  let b : NzElt 𝔟 := ⟨c.out.1.2, c.out.2.2.1, hc⟩
  obtain ⟨ε, hε⟩ : ∃ ε : (𝓞 F)ˣ,
      rep (Quotient.mk (unitRel 𝔟) b : NzCls 𝔟) = ((ε : 𝓞 F) : F) * c.out.1.2 :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (unitRel 𝔟) b)).symm
  have ha : ((ε : 𝓞 F) : F) * c.out.1.1 ∈ latM 𝔞 := by
    have hs := (latM 𝔞 : Submodule (𝓞 F) F).smul_mem (ε : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at hs
  refine ⟨⟨(Quotient.mk (unitRel 𝔟) b : NzCls 𝔟), ⟨_, ha⟩⟩, ?_⟩
  apply Subtype.ext
  show Quotient.mk (latRel 𝔞 𝔟) (pairOf _) = c
  conv_rhs => rw [← Quotient.out_eq c]
  exact (Quotient.sound (s := latRel 𝔞 𝔟) (a := c.out) ⟨ε, rfl, hε⟩).symm

theorem exists_equiv : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (fibreMap 𝔞 𝔟) ⟨fibreMap_injective 𝔞 𝔟, fibreMap_surjective 𝔞 𝔟⟩, ?_⟩
  intro k hk σ z x
  exact eisClass_mk 𝔞 𝔟 hk σ z (pairOf x)

end GlobalTheory.LatFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFreeEtaleLift
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem ker_le_jacobson_of_factor {S T F : Type} [CommRing S] [CommRing T] [FunLike F S T]
    [RingHomClass F S T] (g : F)
    (h : ∀ n : Ideal S, n.IsMaximal → ∃ τ : T →+* S ⧸ n, ∀ x, τ (g x) = Ideal.Quotient.mk n x) :
    RingHom.ker g ≤ (⊥ : Ideal S).jacobson := by
  intro x hx
  refine GlobalTheory.mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_
  obtain ⟨τ, hτ⟩ := h n hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hτ, RingHom.mem_ker.1 hx, map_zero]

def residueToQuot (R : Type) [CommRing R] [IsLocalRing R] {S : Type} [CommRing S] [Algebra R S]
    [Module.Finite R S] (n : Ideal S) [n.IsMaximal] : ResidueField R →ₐ[R] S ⧸ n :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) fun a ha ↦ by
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite n] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

variable {R : Type} [CommRing R] [HenselianLocalRing R] (I : Ideal R)

abbrev algQuotResidue (hI : I ≤ maximalIdeal R) : Algebra (R ⧸ I) (ResidueField R) :=
  (Ideal.Quotient.factor hI : R ⧸ I →+* R ⧸ maximalIdeal R).toAlgebra

theorem exists_lift (hI : I ≤ maximalIdeal R) (E : Type) [CommRing E] [Algebra (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    [Algebra.Etale (R ⧸ I) E] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Algebra.Etale R B ∧
      Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] E) := by
  letI := algQuotResidue I hI
  have : IsScalarTower R (R ⧸ I) (ResidueField R) := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hk : Function.Surjective (algebraMap (R ⧸ I) (ResidueField R)) := fun y ↦ by
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  letI : Algebra R E := ((algebraMap (R ⧸ I) E).comp (algebraMap R (R ⧸ I))).toAlgebra
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R E := .trans (R ⧸ I) E
  obtain ⟨B, _, _, hBfin, hBet, ⟨e⟩⟩ :=
    GlobalTheory.exists_etale_lift_of_etale.{0, 0} R (ResidueField R ⊗[R ⧸ I] E)
  refine ⟨B, inferInstance, inferInstance, hBfin, hBet, ?_⟩
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R ⧸ I] E) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R] B) := .of_algebraMap_eq fun _ ↦ rfl

  let πE : E →ₐ[R ⧸ I] ResidueField R ⊗[R ⧸ I] E := Algebra.TensorProduct.includeRight
  have hπE : Function.Surjective πE := Algebra.TensorProduct.includeRight_surjective _ hk
  have hkerE : RingHom.ker πE ≤ (⊥ : Ideal E).jacobson := by
    refine ker_le_jacobson_of_factor πE fun n hn ↦ ?_
    let σ := (residueToQuot R n).extendScalarsOfSurjective hsurj
    let τ := Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ (R ⧸ I) n) fun _ _ ↦ .all _ _
    exact ⟨τ.toRingHom, fun x ↦ by simp [τ, πE]⟩

  let J := I.map (algebraMap R B)
  have hJ : ∀ (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T),
      (∀ r ∈ I, algebraMap R T r = 0) → ∀ a ∈ J, g a = 0 := fun T _ _ g hT a ha ↦ by
    have : J ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      exact hT r hr
    exact this ha
  have hres : ∀ r ∈ I, algebraMap R (ResidueField R ⊗[R] B) r = 0 := fun r hr ↦ by
    have h0 : algebraMap R (ResidueField R) r = 0 := (residue_eq_zero_iff r).2 (hI hr)
    rw [IsScalarTower.algebraMap_apply R (ResidueField R), h0, map_zero]
  let πB₀ : B ⧸ J →ₐ[R] ResidueField R ⊗[R] B :=
    Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeRight (hJ _ _ hres)
  let πB : B ⧸ J →ₐ[R ⧸ I] ResidueField R ⊗[R] B := πB₀.extendScalarsOfSurjective hsurj
  have hπB_mk : ∀ b : B, πB (Ideal.Quotient.mk J b) = 1 ⊗ₜ b := fun b ↦ rfl
  have hπB : Function.Surjective πB := fun y ↦ by
    obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B residue_surjective y
    exact ⟨Ideal.Quotient.mk J b, rfl⟩
  have hkerB : RingHom.ker πB ≤ (⊥ : Ideal (B ⧸ J)).jacobson := by
    refine ker_le_jacobson_of_factor πB fun n hn ↦ ?_
    let τ := Algebra.TensorProduct.lift (residueToQuot R n)
      ((Ideal.Quotient.mkₐ R n).comp (Ideal.Quotient.mkₐ R J)) fun _ _ ↦ .all _ _
    refine ⟨τ.toRingHom, fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπB_mk]
    simp [τ]

  obtain ⟨φ, hφ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
    (πE.restrictScalars R) hπE hkerE).2
    ((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have hφb : ∀ b, πE (φ b) = e (1 ⊗ₜ b) := fun b ↦ congr($hφ b)

  obtain ⟨ψ, hψ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
    πB hπB hkerB).2 ((e.symm.toAlgHom.restrictScalars (R ⧸ I)).comp πE)
  have hψx : ∀ x, πB (ψ x) = e.symm (πE x) := fun x ↦ congr($hψ x)
  have hEI : ∀ r ∈ I, algebraMap R E r = 0 := fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  let φ' : B ⧸ J →ₐ[R ⧸ I] E := (Ideal.Quotient.liftₐ J φ (hJ _ _ hEI)).extendScalarsOfSurjective hsurj
  have hφ'_mk : ∀ b, φ' (Ideal.Quotient.mk J b) = φ b := fun b ↦ rfl
  have key : ∀ y, πE (φ' y) = e (πB y) := fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hφ'_mk, hφb, hπB_mk]
  have h1 : φ'.comp ψ = AlgHom.id (R ⧸ I) E := by
    refine (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
      πE hπE hkerE).1 (AlgHom.ext fun x ↦ ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, key, hψx, AlgEquiv.apply_symm_apply]
  have h2 : ψ.comp φ' = AlgHom.id (R ⧸ I) (B ⧸ J) := by
    have H := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
      (πB.restrictScalars R) hπB hkerB).1
      (a₁ := (ψ.restrictScalars R).comp φ) (a₂ := Ideal.Quotient.mkₐ R J) (AlgHom.ext fun b ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [hψx, hφb, AlgEquiv.symm_apply_apply, hπB_mk])
    refine AlgHom.ext fun y ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AlgHom.comp_apply, AlgHom.id_apply, hφ'_mk]
    simpa using congr($H b)
  exact ⟨AlgEquiv.ofAlgHom φ' ψ h1 h2⟩

end GlobalTheory.EtaleLiftQuot

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem exists_finite_free_etale_lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E]
    [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E]
    [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B),
      Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧
        Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  intro R _ _ _ hc f hf E _ _ _ _
  have : HenselianRing R (maximalIdeal R) := @IsAdicComplete.henselianRing R _ _ hc
  have : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨B, _, _, h₁, h₂, h₃⟩ :=
    exists_lift (Ideal.span {f}) ((Ideal.span_singleton_le_iff_mem _).2 hf) E
  exact ⟨B, inferInstance, inferInstance, h₁, Module.free_of_flat_of_isLocalRing, h₂, h₃⟩

end GlobalTheory.EtaleLiftQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixedStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  first | exact @GlobalTheory.exists_average_fixed_approx_of_fixed | exact GlobalTheory.exists_average_fixed_approx_of_fixed | (intros; apply GlobalTheory.exists_average_fixed_approx_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullbackStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  first | exact @GlobalTheory.FlatHilbAff.exists_flat_ideal | exact GlobalTheory.FlatHilbAff.exists_flat_ideal | (intros; apply GlobalTheory.FlatHilbAff.exists_flat_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopenStatement
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U → ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧ ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  first | exact @GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | exact GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | (intros; apply GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafComapEqOfOpenCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace GlobalTheory.IdealGlue

theorem exists_comap_eq : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  intro X ι V f hf hcov J hJ
  exact idealSheaf_glue_of_openImmersions (fun 𝒜 h1 h2 k h3 => GlobalTheory.T.exists_idealSheafData_of_compatible_ideals 𝒜 h1 h2 k h3)
    V f hf (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩) J hJ

end GlobalTheory.IdealGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε → ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first | exact @GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | exact GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | (intros; apply GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 → ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first | exact @GlobalTheory.PadicEmb.exists_embedding | exact GlobalTheory.PadicEmb.exists_embedding | (intros; apply GlobalTheory.PadicEmb.exists_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebraStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  first | exact @GlobalTheory.quotient_base_change_invariant_derivations | exact GlobalTheory.quotient_base_change_invariant_derivations | (intros; apply GlobalTheory.quotient_base_change_invariant_derivations <;> assumption)
end

