import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCont

open IsLocalRing

theorem continuous_of_le_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (h : maximalIdeal A ≤ (maximalIdeal B).comap φ) : Continuous φ := by
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [isAdic_iff] at hA hB
  intro s hs
  simp only [map_zero] at hs
  obtain ⟨n, hn⟩ := hB.2 s hs
  have h1 : ((maximalIdeal A ^ n : Ideal A) : Set A) ∈ nhds (0 : A) :=
    (hA.1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.mem_map.2 (Filter.mem_of_superset h1 fun a ha => hn ?_)
  have : (maximalIdeal A ^ n).map φ ≤ maximalIdeal B ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n
  exact this (Ideal.mem_map_of_mem φ ha)

theorem comap_maximalIdeal_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))

theorem p_mem_maximalIdeal {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : ((p : ℕ) : O) ∈ maximalIdeal O := by
  have hp : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  rw [← comap_maximalIdeal_padicInt O] at hp
  simpa using hp

theorem le_comap_of_padicInt {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [IsLocalRing A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A] [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ z, φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[p] B z) : maximalIdeal A ≤ (maximalIdeal B).comap φ := by
  have hc : ((maximalIdeal B).comap φ).comap (algebraMap ℤ_[p] A) = maximalIdeal ℤ_[p] := by
    rw [Ideal.comap_comap, ← comap_maximalIdeal_padicInt B]
    congr 1
    exact RingHom.ext hφ
  haveI : ((maximalIdeal B).comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[p]) _ (by rw [hc]; infer_instance)
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem continuous_of_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = q) {A B : Type} [CommRing A] [IsLocalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [IsLocalRing B]
    [Algebra ℤ_[q] B] [Module.Finite ℤ_[q] B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[q] B z') : Continuous φ := by
  subst hpq
  exact continuous_of_le_comap hA hB φ (le_comap_of_padicInt φ fun z => hφ z z HEq.rfl)

theorem continuous_algebraMap_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (maximalIdeal O)) :
    Continuous (algebraMap ℤ_[p] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] O) ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[p]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (p_mem_maximalIdeal O) n)

section Units

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_units {O : Type} [Monoid O] [TopologicalSpace O] (φ : Γ →* Oˣ)
    (h : Continuous fun g => (φ g : O)) : Continuous φ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((φ g)⁻¹ : Oˣ).val) = fun g => (φ g⁻¹ : O) := by
    funext g; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem continuous_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (f : A →* B)
    (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

theorem continuous_of_isOpen_ker {N : Type} [Group N] [TopologicalSpace N] (φ : Γ →* N)
    (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine IsLocallyConstant.continuous fun s => ?_
  have e : φ ⁻¹' s = ⋃ x ∈ φ ⁻¹' s, (fun g => x⁻¹ * g) ⁻¹' (φ.ker : Set Γ) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, exists_prop]
    constructor
    · intro hg; exact ⟨g, hg, inv_mul_cancel _⟩
    · rintro ⟨x, hx, hxg⟩
      rw [inv_mul_eq_one] at hxg
      rwa [← hxg]
  rw [e]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

end Units

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem chiN_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  intro D M C hR X hS twC ψ0 hP htw hker i c
  have hadic : ∀ j w, IsAdic (maximalIdeal (OcC X j w)) := oc_adic X
  have htwc : ∀ j w, Continuous (twC j w) := fun j w =>
    continuous_of_heq (C.twI_l w) (D.ntw.twistBaseCoefficientRing_isAdic (C.twI w)) (hadic j w) (twC j w) (htw j w)
  have h1 : Continuous (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i)
      (C.sd (wOf (base M C hR X hS) i))) :=
    continuous_units _ (D.ntw.twistCharacterFamily_continuous _ _ _)
  have h2 : Continuous (psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)) :=
    continuous_of_isOpen_ker _ (hker _ _)
  have h3 : Continuous (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (htwc _ _)
  haveI : Fact (lOf (base M C hR X hS) i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).algOc _ _
  haveI : Module.Finite ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).finOc _ _
  have h4 : Continuous (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (continuous_algebraMap_padicInt _ (hadic _ _))
  have h5 := continuous_cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i)
  refine Units.continuous_val.comp ?_
  change Continuous fun g =>
    ((show (OOf (base M C hR X hS) i)ˣ from (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom)
      (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i) (C.sd (wOf (base M C hR X hS) i)) g)) *
      (show (OOf (base M C hR X hS) i)ˣ from psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i) g)) *
    (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom
      (cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i) g)) ^ (-((c : ℤ) - 1))
  exact ((h3.comp h1).mul h2).mul ((h4.comp h5).zpow _)

end GlobalTheory.HeckeLocCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

theorem isLocalRing_of_congr {O X : Type} [CommRing O] [IsLocalRing O] [Finite X] [Nonempty X] (T : Subalgebra O (X → O))
    (h : ∀ f ∈ T, ∀ x y, f x - f y ∈ IsLocalRing.maximalIdeal O) : IsLocalRing T := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f := by
    intro f hx
    have : Algebra.IsIntegral T (X → O) := Algebra.IsIntegral.tower_top O
    have hu : IsUnit (algebraMap T (X → O) f) := by
      refine Pi.isUnit_iff.2 fun y => ?_
      by_contra hy
      have h1 := add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)
      exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx
    have hl := RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O))
      (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective
    exact hl.map_nonunit f hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))

theorem sub_mem_of_ker_eq {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] (ψ φ : A →ₐ[O] O)
    (h : RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom) = RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom))
    (a : A) : ψ a - φ a ∈ IsLocalRing.maximalIdeal O := by
  have h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom) := by
    rw [RingHom.mem_ker]; simp
  rw [← h, RingHom.mem_ker] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa using h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (i : LocT B), IsLocalRing (TOf B i) := by
  intro R H what₂ B hs hd i
  have := xFin_of hs hd i
  have := xNe_of hs hd i
  refine isLocalRing_of_congr (TOf B i) fun f hf x y => ?_
  rw [← Ideal.Quotient.eq]
  unfold TOf at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    refine Ideal.Quotient.eq.2 ?_
    simp only [hTfun, dif_pos hvk]
    exact sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _
  | algebraMap r => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]

end GlobalTheory.HeckeLocN.TLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmax

theorem tensor_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[maximalRealSubfield L] a) = x ⊗ₜ[maximalRealSubfield L] (a v) := by
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul]
  rfl

theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨A, B, hAB⟩ := tensor_decomp b z
  have hoff : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB, map_add, compAt_tmul, compAt_tmul] at h
    exact tensor_decomp_zero b _ _ h
  have hA : A = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).1
  have hB : B = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).2
  rw [hAB, hA, hB]; simp

open Classical in

def sgl (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite ?_
    intro w hw
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩

omit [IsCMField L] in
theorem sgl_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : sgl L v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r

omit [IsCMField L] in
theorem sgl_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) {w} (hw : w ≠ v) : sgl L v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) hw r

omit [IsCMField L] in
theorem one_tmul_sgl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L))
    (hr : r ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v r : AL L) ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨sgl L v r, fun w => ?_, rfl⟩)
  rcases eq_or_ne w v with rfl | hw
  · rw [sgl_same]; exact hr
  · rw [sgl_ne L v r hw]; exact zero_mem _

omit [IsCMField L] in

theorem exists_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hy : y ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    ∃ Y ∈ ALint L, compAt L v Y = y := by
  have key : tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ≤ (ALint L).map (compAt L v) := by
    rw [tensInt, Subring.closure_le]
    rintro _ (⟨⟨_, s, rfl⟩, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨(s : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L),
        Subring.subset_closure (Or.inl ⟨s, rfl⟩), ?_⟩
      rw [compAt_tmul]; rfl
    · refine ⟨_, one_tmul_sgl_mem L v r r.2, ?_⟩
      rw [compAt_tmul, sgl_same]
  exact key hy

theorem mem_ALint_of_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : AL L)
    (hoff : ∀ w, w ≠ v → compAt L w x = 0)
    (hv : compAt L v x ∈ tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    x ∈ ALint L := by
  obtain ⟨Y, hY, hYv⟩ := exists_lift L v _ hv
  have h : x - Y * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, compAt_tmul]
    rcases eq_or_ne w v with rfl | hw
    · rw [sgl_same, hYv, ← Algebra.TensorProduct.one_def, mul_one, sub_self]
    · rw [sgl_ne L v 1 hw, hoff w hw, tmul_zero, mul_zero, sub_self]
  rw [sub_eq_zero.1 h]
  exact Subring.mul_mem _ hY (one_tmul_sgl_mem L v 1 (one_mem _))

theorem entries_mem_of_range {K : Type} [Field K] (S : Subring K) {n : ℕ} (P : GL (Fin n) K)
    (hP : P ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range) (i j : Fin n) :
    (P : Matrix (Fin n) (Fin n) K) i j ∈ S := by
  obtain ⟨Q, rfl⟩ := hP
  exact ((Q : Matrix (Fin n) (Fin n) S) i j).2

theorem mem_Umax_of_trivOutside_of_loc_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  intro L _ _ _ n v w Dv z hz hint i j
  have hP := entries_mem_of_range _ _ Dv.Pint
  have hP' := entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hg : Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) =
      Dv.P * Dv.loc z * Dv.P⁻¹ := by
    unfold InertDatum.loc
    group
  have he : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) ∈
      intL (w.adicCompletion L) := by
    have h1 : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) =
        ((Dv.P * Dv.loc z * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j := by
      rw [← hg]; rfl
    rw [h1]
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
      (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP i l) (hint l k)) (hP' k j)
  have hv := (Dv.integ _).2 he
  have hone : ∀ {R : Type} [CommRing R] (S : Subring R), (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
    intro R _ S
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hc : ∀ u, compAt L u ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro u
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hd : (z.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈
      ALint L := by
    apply mem_ALint_of_supported L v
    · intro u hu
      have h := congrFun (congrFun (hz u hu) i) j
      rw [map_sub, hc, ← h, Matrix.map_apply, sub_self]
    · rw [map_sub, hc]
      exact Subring.sub_mem _ hv (hone _)
  have := Subring.add_mem _ hd (hone (ALint L))
  rwa [sub_add_cancel] at this

end GlobalTheory.InertUmax
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedLocTiedOfBuilt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem locTied_any (D' : D7) : Nonempty (Formalism.L2.LocTied D') :=
  ⟨⟨fun l _ => GlobalTheory.LocArith.arithTied l (D'.loc l), fun i w hw => D'.nbr_ind i w hw,
    fun i w hw => D'.ntwbr_ind i w hw⟩⟩

theorem nTied_locTied_of_built : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), CgCmp hL → ∀ (D' : D7) (b : NBuilt hL D'),
    Nonempty (NormalizedHeckeDataPlaceholder D') ∧ Nonempty (Formalism.L2.LocTied D') := by
  intro hL hcg D' b
  exact ⟨⟨⟨⟩⟩, locTied_any D'⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSumStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_sum | exact GlobalTheory.GoodMetric.PolyRep.lie_sum | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquareStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | exact GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_wedge2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProductStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_tensor | exact GlobalTheory.GoodMetric.PolyRep.lie_tensor | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  first | exact @GlobalTheory.TopSpan.proj_span | exact GlobalTheory.TopSpan.proj_span | (intros; apply GlobalTheory.TopSpan.proj_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaOrderStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_order : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ), ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))}, Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  first | exact @GlobalTheory.TrueGeo.PlaceFormula.main | exact GlobalTheory.TrueGeo.PlaceFormula.main | (intros; apply GlobalTheory.TrueGeo.PlaceFormula.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in

theorem reFace_zero_parts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hP hH hZ
  have h1 := pins_updS R F cG (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) hP (scal_zeroLam R F Dc Sp Zsc hZ hP.char.scal)
  have h2 := prim_updS R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.prim (zeroLam_pos R F (Zsc (R.toCx3 F).zs).l6m hH.prim.posScal.2)
    (thmB_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hZ hH.prim.thmB) (thmA_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.thmA) (galD_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.scalConj)
  have h3 := Holds.mk (reFace_prim (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) h2)
    (further_face_statements_independent_of_error (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) (furtherRows_updatedScalars R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.aux)) hH.ok hH.sep
  have h4 := reFace_errEq (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc
  have h5 : ∀ i t p v, R.EEp3 p ≠ ⊥ → zeroLam R F (Zsc (R.toCx3 F).zs).l6m i t p v = R.lam3 i t p v :=
    fun i t p v hp => zeroLam_of_ne R F _ (hZ p hp i).1 fun hv => (hZ p hp i).2 v hv
  have h6 := read_updS_keep R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc)
    (XE_updS_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hP.char hH.prim hH.ok hH.sep hZ) X0 Y Z
  refine ⟨R.kap, (zeroLam R F (Zsc (R.toCx3 F).zs).l6m), (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h3 :))
  · exact (by with_unfolding_all exact (h4 :))
  · exact (by with_unfolding_all exact (h5 :))
  · exact (by with_unfolding_all exact (h6 :))

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCardStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_embeddings_card : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  first | exact @GlobalTheory.TrueGeo.ResidueCard.main | exact GlobalTheory.TrueGeo.ResidueCard.main | (intros; apply GlobalTheory.TrueGeo.ResidueCard.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFiniteTypes_isotypicParts_span_orthogonal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (P : principalLevelFrame.RowPsi V D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Inputs D → V.SigOK → IsInfFam θ → StdFrame hF P → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → (∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧ e = ∑ g ∈ s, c g • principalLevelFrame.rtA g) → (⨆ π, principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π) = goodPart θ M (levS V β L) (levChi V β L) e ∧ ∀ π π', ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π, ∀ y ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π', ipM M μ 𝓕 x y = 0 := by
  first | exact @GlobalTheory.FinTypesRows.isotL_span_orth | exact GlobalTheory.FinTypesRows.isotL_span_orth | (intros; apply GlobalTheory.FinTypesRows.isotL_span_orth <;> assumption)
end

