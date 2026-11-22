import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFinitelyGeneratedModOpen
section
noncomputable section

open Matrix GlobalTheory.LKRes ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct Classical

namespace GlobalTheory.CentFG

theorem field_case (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hL : FiniteDimensional ℚ_[p] L) (n : ℕ) (N : GL (Fin n) L) (hN : N.val.charpoly.Separable) :
    ∃ G : Finset (GL (Fin n) L), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) L)) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L))) := by
  obtain ⟨v, c, hv⟩ := GlobalTheory.T.centralizer_bounded_valuation_kernel p L hL n N hN
  have hfg : v.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule v.range.toAddSubgroup)).1
      (IsNoetherian.noetherian (R := ℤ) (M := Additive (Multiplicative (Fin n → ℤ))) _)
  obtain ⟨S, hS⟩ := hfg
  have hpre : ∀ s : S, ∃ z : Subgroup.centralizer {N}, v z = s := fun s =>
    (show (s : Multiplicative (Fin n → ℤ)) ∈ v.range from hS ▸ Subgroup.subset_closure s.2)
  choose pre hpre using hpre
  let B : Subgroup (GL (Fin n) L) := v.ker.map (Subgroup.centralizer {N}).subtype
  obtain ⟨T, hT, hTB⟩ := GlobalTheory.T.bounded_subgroup_finite_cosets p L hL n B c (by
    rintro _ ⟨z, hz, rfl⟩ i j
    exact hv z hz i j)
  refine ⟨Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_union.1 hg with h | h
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 h
      exact (pre s).2
    · obtain ⟨z, -, rfl⟩ := hT g h
      exact z.2
  · intro z hz
    set C := Subgroup.closure (((Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T :
      Finset _) : Set (GL (Fin n) L)) ∪ ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L)))
    let W : Subgroup (Subgroup.centralizer {N}) := Subgroup.closure (Set.range pre)
    have hW : W.map v = v.range := by
      rw [MonoidHom.map_closure, ← hS]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        rw [hpre]; exact s.2
      · intro hx
        exact ⟨pre ⟨x, hx⟩, ⟨_, rfl⟩, hpre _⟩
    obtain ⟨w, hw, hwv⟩ : v ⟨z, hz⟩ ∈ W.map v := by rw [hW]; exact ⟨_, rfl⟩
    have hWle : W ≤ C.comap (Subgroup.centralizer {N}).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨s, rfl⟩
      refine Subgroup.subset_closure (Or.inl ?_)
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
        Set.mem_range]
      exact Or.inl ⟨s, rfl⟩
    have hWC : ∀ y ∈ W, (y : GL (Fin n) L) ∈ C := fun y hy => hWle hy
    have hk : w⁻¹ * ⟨z, hz⟩ ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
    obtain ⟨t, htT, ht⟩ := hTB _ ⟨_, hk, rfl⟩
    have htZ : t ∈ Subgroup.centralizer {N} := by
      obtain ⟨y, -, rfl⟩ := hT t htT; exact y.2
    have hrest : t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z) ∈ C := by
      refine Subgroup.subset_closure (Or.inr ⟨?_, ?_⟩)
      · exact (Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem htZ)
          ((Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem w.2) hz)
      · simpa using ht
    have htC : t ∈ C := Subgroup.subset_closure (Or.inl (by simp [htT]))
    have : z = (w : GL (Fin n) L) * t * (t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z)) := by group
    rw [this]
    exact C.mul_mem (C.mul_mem (hWC w hw) htC) hrest

theorem centralizer_le_closure : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  intro p _ K hK n r hr N hN
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  obtain ⟨e, -, -, -, -, -, -, hint⟩ := GlobalTheory.T.unramified_extension_product_decomposition p K hK f r hf hr
  have hd : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right _ hr
  have hfin : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) hd)
  generalize Nat.gcd f r = g at *
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  exact GlobalTheory.T.centralizer_finite_generation_transfer _ _ k n e (intKQ p K r) (GlobalTheory.LKLoc.intR p K (r / (k + 1))) hint
    (fun N' hN' => field_case p _ hfin n N' hN') N hN

end GlobalTheory.CentFG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

theorem atPl_eq_zero_of_common {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : ι) (F : Set (Module.End ℂ V)) (g : Module.End ℂ V) (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0)
    (T : ⨂[ℂ] _ : ι, V) (hT : ∀ L ∈ F, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w L T = 0) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.FactorKernel.contr w f T) = 0 := hg _ fun L hL => by
    rw [← GlobalTheory.FactorKernel.contr_atPl, hT L hL, map_zero]
  have h := GlobalTheory.FactorKernel.dual_contr w f (f w) (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T)
  rw [GlobalTheory.FactorKernel.contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

theorem atPl_sub_smul_one {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : ι) (L : Module.End ℂ V) (c : ℂ) (T : ⨂[ℂ] _ : ι, V) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (L - c • 1) T =
      GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w L T - c • T := by
  have e1 : L - c • 1 = L + (-c) • (1 : Module.End ℂ V) := by rw [neg_smul, sub_eq_add_neg]
  have e2 : GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (1 : Module.End ℂ V) = 1 := by
    unfold GlobalTheory.RealLift.atPl
    have : Function.update (fun i : ι => (LinearMap.id : V →ₗ[ℂ] V)) w (1 : Module.End ℂ V) =
        fun _ => LinearMap.id := Function.update_eq_self_iff.2 rfl
    rw [this, PiTensorProduct.map_id]; rfl
  rw [e1]
  unfold GlobalTheory.RealLift.atPl at e2 ⊢
  rw [PiTensorProduct.map_update_add, PiTensorProduct.map_update_smul, e2]
  simp [sub_eq_add_neg]

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

theorem exists_proj_of_graded {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ))
    (hK : ∀ f ∈ K, ∀ n, homogeneousComponent n f ∈ K) :
    ∃ p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ f, p f ∈ K) ∧ (∀ f ∈ K, p f = f) ∧
      ∀ f, (p f).totalDegree ≤ f.totalDegree := by
  classical
  have hex : ∀ n : ℕ, ∃ g : MvPolynomial σ ℂ →ₗ[ℂ] ↥(K ⊓ homogeneousSubmodule σ ℂ n),
      g ∘ₗ (K ⊓ homogeneousSubmodule σ ℂ n).subtype = LinearMap.id := fun n =>
    LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
  choose g hg using hex
  let q : ℕ → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ := fun n =>
    (K ⊓ homogeneousSubmodule σ ℂ n).subtype ∘ₗ g n ∘ₗ homogeneousComponent n
  have hq0 : ∀ f : MvPolynomial σ ℂ, ∀ N, f.totalDegree < N →
      ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = ∑ i ∈ Finset.range N, q i f := by
    intro f N hN
    apply Finset.sum_subset (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    intro i _ hi
    have : f.totalDegree < i := by simp at hi; omega
    simp [q, homogeneousComponent_eq_zero _ _ this]
  let p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
    { toFun := fun f => ∑ i ∈ Finset.range (f.totalDegree + 1), q i f
      map_add' := fun f f' => by
        rw [hq0 f (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 f' (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 (f + f') (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [hq0 f (max f.totalDegree (c • f).totalDegree + 1) (by omega),
          hq0 (c • f) (max f.totalDegree (c • f).totalDegree + 1) (by omega), Finset.smul_sum]
        simp only [map_smul] }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro f
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f ∈ K
    exact Submodule.sum_mem _ fun i _ => (g i (homogeneousComponent i f)).2.1
  · intro f hf
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = f
    conv_rhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : homogeneousComponent i f ∈ K ⊓ homogeneousSubmodule σ ℂ i :=
      ⟨hK f hf i, homogeneousComponent_isHomogeneous i f⟩
    have := congrArg (fun h => ((h ⟨_, hm⟩ : ↥(K ⊓ homogeneousSubmodule σ ℂ i)) : MvPolynomial σ ℂ)) (hg i)
    simpa [q] using this
  · intro f
    show (∑ i ∈ Finset.range (f.totalDegree + 1), q i f).totalDegree ≤ f.totalDegree
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)
    have hi' : i ≤ f.totalDegree := by simp at hi; omega
    have hh : (q i f).IsHomogeneous i := (g i (homogeneousComponent i f)).2.2
    by_cases h0 : q i f = 0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · rw [hh.totalDegree h0]; exact hi'

theorem homogeneousComponent_fockAct1 {P Q R S : ℕ} (X : Mat P Q) (hX : IsKC X) (n : ℕ) (f : Pol P Q R S) :
    homogeneousComponent n (fockAct1 P Q R S X f) = fockAct1 P Q R S X (homogeneousComponent n f) := by
  classical
  have hh : ∀ i, fockAct1 P Q R S X (homogeneousComponent i f) ∈ homogeneousSubmodule (Ix P Q × Ix R S) ℂ i :=
    fun i => GlobalTheory.FockAlg.MinFirst.kStable_homog i X hX _ (homogeneousComponent_isHomogeneous i f)
  conv_lhs => rw [← sum_homogeneousComponent f, map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem (hh _)]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have : f.totalDegree < n := by simp at h; omega
    rw [homogeneousComponent_eq_zero _ _ this, map_zero]

theorem homogeneousComponent_mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Pol P Q R S) (hf : f ∈ chiOne P Q R S x) (n : ℕ) :
    homogeneousComponent n f ∈ chiOne P Q R S x := by
  rw [mem_chiOne] at hf ⊢
  intro X hX
  rw [← homogeneousComponent_fockAct1 X hX, hf X hX, map_smul]

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr

open MvPolynomial Formalism.BasicNotions.TH TensProj

theorem mem_span_tprod_chiOne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (x : ι → ℚ) (m : ℕ)
    (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
    T ∈ Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧
      ∑ w, (g w).totalDegree ≤ m ∧ U = PiTensorProduct.tprod ℂ g} := by
  intro ι _ _ P Q R S x m T hT
  classical
  obtain ⟨hchi, hdeg⟩ := Submodule.mem_inf.1 hT
  have hex : ∀ w, ∃ p : Pol P Q R S →ₗ[ℂ] Pol P Q R S, (∀ f, p f ∈ chiOne P Q R S (x w)) ∧
      (∀ f ∈ chiOne P Q R S (x w), p f = f) ∧ ∀ f, (p f).totalDegree ≤ f.totalDegree := fun w =>
    exists_proj_of_graded _ (homogeneousComponent_mem_chiOne (x w))
  choose p hpK hpid hpdeg using hex

  have hfix : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : ι => Pol P Q R S) w (p w) T = T := by
    intro w
    have h0 := atPl_eq_zero_of_common w
      {L | ∃ X : Mat P Q, IsKC X ∧ L = fockAct1 P Q R S X - ((x w : ℂ) * X.trace) • 1}
      (p w - 1) (fun v hv => by
        have hv' : v ∈ chiOne P Q R S (x w) := by
          rw [mem_chiOne]
          intro X hX
          have := hv _ ⟨X, hX, rfl⟩
          rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v hv', sub_self])
      T (by
        rintro L ⟨X, hX, rfl⟩
        rw [atPl_sub_smul_one, (mem_chiPart x T).1 hchi w X hX, sub_self])
    have h1 := atPl_sub_smul_one w (p w) 1 T
    simp only [one_smul] at h1
    rw [h0] at h1
    exact (sub_eq_zero.1 h1.symm)

  have hmap : ∀ s : Finset ι,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) T = T := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) =
          fun w => (Function.update (fun _ => (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hT' : PiTensorProduct.map p T = T := by
    have := hmap Finset.univ
    simpa using this
  rw [← hT']

  have hle : degLE ι P Q R S m ≤ (Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S,
      (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧ ∑ w, (g w).totalDegree ≤ m ∧
        U = PiTensorProduct.tprod ℂ g}).comap (PiTensorProduct.map p) := by
    refine Submodule.span_le.2 ?_
    rintro U ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, PiTensorProduct.map_tprod]
    exact Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _,
      (Finset.sum_le_sum fun w _ => hpdeg w (f w)).trans hf, rfl⟩
  exact hle hdeg

end GlobalTheory.KFixIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.CMConjInvol

theorem cm_conj_invol_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x :=
  fun _ _ _ _ _ _ _ _ h => ⟨GlobalTheory.HermLineZeros.conj_invol h, GlobalTheory.HermLineZeros.exists_of_fixed h⟩

end GlobalTheory.CMConjInvol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSignsStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EtaSignReal.eta_eq_prod_sign | exact GlobalTheory.EtaSignReal.eta_eq_prod_sign | (intros; apply GlobalTheory.EtaSignReal.eta_eq_prod_sign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB), cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) → Subsingleton (coh (LB.toMod N) q) := by
  first | exact @GlobalTheory.Div.coh_subsingleton_of_cls_eq | exact GlobalTheory.Div.coh_subsingleton_of_cls_eq | (intros; apply GlobalTheory.Div.coh_subsingleton_of_cls_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCoverStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @GlobalTheory.coh_subsingleton_of_disjoint_cover | exact GlobalTheory.coh_subsingleton_of_disjoint_cover | (intros; apply GlobalTheory.coh_subsingleton_of_disjoint_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteAtSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_different (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ P.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E) := by
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := D.host.isCMField_hostE
    exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  haveI := P.isPrime
  exact not_dvd_differentIdeal_iff.2 (Algebra.unramified_iff_forall.1 hU ⟨P.asIdeal, P.isPrime⟩)

end GlobalTheory.HeckeOrthSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianLogOneAddNormSqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHessian_log_one_add_normSq : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  first | exact @GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq | exact GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq | (intros; apply GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_parts_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  first | exact @GlobalTheory.Div.parts_orth_complex | exact GlobalTheory.Div.parts_orth_complex | (intros; apply GlobalTheory.Div.parts_orth_complex <;> assumption)
end

