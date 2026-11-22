import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct Topology

namespace GlobalTheory.IntDense

theorem mem_of_isClosed (F : Type) [Field F] [NumberField F] {C : Set (FiniteAdeleRing (𝓞 F) F)}
    (hC : IsClosed C) (h : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ C)
    (α : FiniteAdeleRing (𝓞 F) F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) : α ∈ C := by
  by_contra hn
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F => α - y := continuous_const.sub continuous_id
  have hU : (fun y : FiniteAdeleRing (𝓞 F) F => α - y) ⁻¹' Cᶜ ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (hC.isOpen_compl.preimage hc).mem_nhds (by simpa using hn)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
  refine hNU β hβ ?_
  change α - N • β ∈ C
  rw [e, add_sub_cancel_right]
  exact h a

theorem addChar_eq_one_of_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  intro F _ _ ψ hψ x h α hα
  have hp : Continuous fun y : Af F => pairA F 0 (y * algebraMap F (Af F) x) :=
    Continuous.prodMk continuous_const (continuous_id.mul continuous_const)
  refine mem_of_isClosed F (C := {y | ψ (pairA F 0 (y * algebraMap F (Af F) x)) = 1})
    (isClosed_eq (hψ.comp hp) continuous_const) (fun a => ?_) α hα
  have := h a
  rwa [map_mul] at this

end GlobalTheory.IntDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinMod

open GlobalTheory.LatVac

theorem exists_finite_mod {W : Type} [AddCommGroup W] {G : Set W} (hG : G.Finite) {k : ℕ} (hk : 0 < k) :
    ∃ R : Set W, R.Finite ∧ ∀ x ∈ Submodule.span ℤ G, ∃ r ∈ R, ∃ u ∈ Submodule.span ℤ G, x = r + k • u := by
  induction G, hG using Set.Finite.induction_on with
  | empty => exact ⟨{0}, Set.finite_singleton _, fun x hx => ⟨0, rfl, 0, zero_mem _, by simpa using hx⟩⟩
  | @insert g G _ _ ih =>
    obtain ⟨R, hR, h⟩ := ih
    refine ⟨Set.image2 (fun (j : ℤ) r => j • g + r) (Set.Ico 0 k) R, (Set.finite_Ico _ _).image2 _ hR,
      fun x hx => ?_⟩
    obtain ⟨c, y, hy, rfl⟩ := Submodule.mem_span_insert.1 hx
    obtain ⟨r, hr, u, hu, rfl⟩ := h y hy
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    refine ⟨_, ⟨c % k, ⟨Int.emod_nonneg _ hk'.ne', Int.emod_lt_of_pos _ hk'⟩, r, hr, rfl⟩,
      (c / k) • g + u, Submodule.mem_span_insert.2 ⟨_, u, hu, rfl⟩, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv c k]
    simp only [add_smul, mul_smul, smul_add, natCast_zsmul]
    abel

theorem exists_int_gen {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module (𝓞 E) M]
    (N : Submodule (𝓞 E) M) (hN : N.FG) :
    ∃ A : Set M, A.Finite ∧ A ⊆ N ∧ ∀ x ∈ N, x ∈ Submodule.span ℤ A := by
  have h1 : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have h2 : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨s, hs⟩ := h2.fg_top
  refine ⟨Subtype.val '' (s : Set N), s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · have : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (s : Set N) := by rw [hs]; trivial
    exact Submodule.apply_mem_span_image_of_mem_span (N.subtype.toAddMonoidHom.toIntLinearMap) this

theorem triadd_mem_span {X Y Z W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    (f : X → Y → Z → W) (h1 : ∀ a a' s t, f (a + a') s t = f a s t + f a' s t)
    (h2 : ∀ a s s' t, f a (s + s') t = f a s t + f a s' t) (h3 : ∀ a s t t', f a s (t + t') = f a s t + f a s t')
    {A : Set X} {B : Set Y} {C : Set Z} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    f a s t ∈ Submodule.span ℤ ((fun p : X × Y × Z => f p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  have gen : ∀ {U : Type} [AddCommGroup U] (g : U → W), (∀ u u', g (u + u') = g u + g u') →
      ∀ (N : Submodule ℤ W) (V : Set U), (∀ u ∈ V, g u ∈ N) → ∀ u ∈ Submodule.span ℤ V, g u ∈ N := by
    intro U _ g hg N V hV u hu
    have : Submodule.span ℤ V ≤ N.comap (AddMonoidHom.mk' g hg).toIntLinearMap := Submodule.span_le.2 hV
    exact this hu
  refine gen (fun a => f a s t) (fun a a' => h1 a a' s t) _ A (fun a ha => ?_) a ha
  refine gen (fun s => f a s t) (fun s s' => h2 a s s' t) _ B (fun s hs => ?_) s hs
  refine gen (fun t => f a s t) (h3 a s) _ C (fun t ht => ?_) t ht
  exact Submodule.subset_span ⟨(a, s, t), ⟨ha, hs, ht⟩, rfl⟩

theorem star_sum_add {E : Type} [CommRing E] [StarRing E] {n : ℕ} (c : E) (s s' g : Fin n → E) :
    c * ∑ k, star ((s + s') k) * g k = c * ∑ k, star (s k) * g k + c * ∑ k, star (s' k) * g k := by
  simp [mul_add, add_mul, Finset.sum_add_distrib]

theorem pair_tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (ε β : Af F) (x : F) (k : ℕ) (a t g : E) :
    pairA F 0 (ε * (algebraMap F _ x + k • β)) ⊗ₜ[F] (a * t * g) =
      pairA F 0 ε ⊗ₜ[F] (algebraMap F E x * a * t * g) + k • (pairA F 0 (ε * β) ⊗ₜ[F] (a * t * g)) := by
  have hp : pairA F 0 (ε * (algebraMap F _ x + k • β)) = x • pairA F 0 ε + k • pairA F 0 (ε * β) := by
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = x • 0 + k • 0
      simp
    · change ε * (algebraMap F _ x + k • β) = x • ε + k • (ε * β)
      rw [mul_add, mul_smul_comm, Algebra.smul_def x, mul_comm ε]
  rw [hp, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def x,
    ← mul_assoc, ← mul_assoc]

theorem add_nsmul_residue_add {W : Type} [AddCommGroup W] (k : ℕ) (y u y' u' : W) :
    y + k • u + (y' + k • u') = y + y' + k • (u + u') := by rw [smul_add]; abel

theorem neg_nsmul_residue {W : Type} [AddCommGroup W] (k : ℕ) (y u : W) : -(y + k • u) = -y + k • -u := by
  rw [smul_neg]; abel

theorem add_nsmul_residue_assoc {W : Type} [AddCommGroup W] (k : ℕ) (r u' u : W) :
    r + k • u' + k • u = r + k • (u' + u) := by rw [smul_add, add_assoc]

variable {D : D7}

theorem genMap_mem_span (S T : HSp D) {A : Set D.host.E} {B : Set (Fin S.rank → D.host.E)}
    {C : Set (Fin T.rank → D.host.E)} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    genMap S T a s t ∈ Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  refine triadd_mem_span (genMap S T) (fun a a' s t => ?_) (fun a s s' t => ?_) (fun a s t t' => ?_) ha hs ht
  · exact Matrix.ext fun i j => (congrArg (· * _) (add_mul a a' (t i))).trans (add_mul _ _ _)
  · exact Matrix.ext fun i j => star_sum_add (a * t i) s s' fun k => S.gram k j
  · exact Matrix.ext fun i j => (congrArg (· * _) (mul_add a (t i) (t' i))).trans (add_mul _ _ _)

open Classical in

def idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop)
    (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemAt F P) = if P v then 1 else 0 := rfl

theorem latO_finite_mod : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ΛS.FG → ΛT.FG → ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (k : ℕ), 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, ∃ r ∈ R, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, t = r + k • u := by
  intro D S T ΛS ΛT hS hT P k hk
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ Submodule.span ℤ G, x ∈ Λ := by
    have : Submodule.span ℤ G ≤ Λ.toIntSubmodule := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
      exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    exact fun x hx => this hx
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨R, hR, h⟩ := exists_finite_mod hG hk
  refine ⟨R, hR, fun w hw => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  obtain ⟨r, hr, u', hu', rfl⟩ := h y hy
  exact ⟨r, hr, u' + u, add_mem (hGΛ _ hu') hu, add_nsmul_residue_assoc k r u' u⟩

end GlobalTheory.LatFinMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacDual

theorem exists_extension {O E V : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (Λ : Submodule O V) (hspan : Submodule.span E (Λ : Set V) = ⊤) (φ : Λ →ₗ[O] O) :
    ∃ ψ : V →ₗ[E] E, ∀ x : Λ, ψ x = algebraMap O E (φ x) := by
  haveI : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun x => by
        rw [Module.End.isUnit_iff]
        have hx : algebraMap O E x ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
        refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap O E x)⁻¹ • b, ?_⟩⟩
        · have h' : algebraMap O E x • a = algebraMap O E x • b := by
            simpa [Module.algebraMap_end_apply] using h
          exact smul_right_injective V hx h'
        · rw [Module.algebraMap_end_apply, ← algebraMap_smul E, smul_smul, mul_inv_cancel₀ hx, one_smul]
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set V) := hspan ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun {a b} h => ⟨1, by rw [Λ.injective_subtype h]⟩ }
  let g : V →ₗ[O] E := IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
    ((Algebra.linearMap O E).comp φ) (IsLocalizedModule.map_units (Algebra.linearMap O E))
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype ((Algebra.linearMap O E).comp φ)
    (IsLocalizedModule.map_units (Algebra.linearMap O E)) x

theorem exists_dual_family {E : Type} [Field E] [NumberField E] [StarRing E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (hG : ∀ i j, star (G i j) = G j i) (hdet : IsUnit G.det)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hsd : ∀ y : Fin r → E, (∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) → y ∈ Λ) :
    ∃ (n : ℕ) (s s' : Fin n → Fin r → E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧
      ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * G k j = if a = j then 1 else 0 := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose ψ hψ using fun i : Fin n => exists_extension Λ hspan ((LinearMap.proj i).comp σ)
  let c : Fin n → Fin r → E := fun i j => ψ i (Pi.single j 1)
  have hc : ∀ i x, ψ i x = ∑ j, x j * c i j := by
    intro i x
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp [c, map_sum]
  let s' : Fin n → Fin r → E := fun i => star (c i ᵥ* G⁻¹)
  have hs' : ∀ i j, ∑ k, star (s' i k) * G k j = c i j := by
    intro i j
    have : (c i ᵥ* G⁻¹) ᵥ* G = c i := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    rw [← congrFun this j]
    simp [s', Matrix.vecMul, dotProduct]
  let s : Fin n → Fin r → E := fun i => f (Pi.single i 1)
  refine ⟨n, s, s', fun i => ⟨(f (Pi.single i 1)).2, hsd _ fun x hx => ?_⟩, fun a j => ?_⟩
  · have h1 : ∑ a, ∑ b, star (x a) * G a b * s' i b = star (ψ i x) := by
      rw [hc, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hs', star_mul', star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', star_star, hG]; ring
    have h2 := hψ i ⟨x, hx⟩
    rw [h1]
    refine ⟨⟨star (ψ i x), ?_⟩, rfl⟩
    have h3 : IsIntegral ℤ (ψ i x) := by
      rw [show ψ i x = _ from h2]
      exact RingOfIntegers.isIntegral_coe _
    exact h3.map (starRingEnd E).toIntAlgHom
  · have key : (∑ i, (ψ i).smulRight (s i) : (Fin r → E) →ₗ[E] (Fin r → E)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun x hx => ?_
      have h1 : f (σ ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hσ ⟨x, hx⟩
      rw [pi_eq_sum_univ' (σ ⟨x, hx⟩), map_sum] at h1
      have h2 := congrArg Λ.subtype h1
      rw [map_sum] at h2
      rw [LinearMap.sum_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [LinearMap.smulRight_apply, show ψ i x = _ from hψ i ⟨x, hx⟩, algebraMap_smul, map_smul, map_smul]
      rfl
    have h := congrFun (LinearMap.congr_fun key (Pi.single j 1)) a
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.id_apply, Pi.single_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs', mul_comm]

theorem dualFamily : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S Λ → ∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0 := by
  intro D S Λ h
  exact exists_dual_family S.gram (gram_star S) (gram_det_isUnit S) Λ h.1.fg h.1.span_eq_top
    fun y hy => (h.2 y).2 hy

end GlobalTheory.LatVacDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdem

theorem idem_alg {T : Type} [CommRing T] (p U R w m : T) (hU : p * U = U) (hR : R * R - R + m * p = 0)
    (hδ : U - 2 * (U * R) = p) (hw : w * w - w + m = 0) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * (1 - w) - U * R) = 0 ∧
      (U * w - U * R) + (U * (1 - w) - U * R) = p := by
  have h2 : (U * w - U * R) * (U * (1 - w) - U * R) = 0 := by
    linear_combination U * U * hR - U * U * hw - m * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] (φ : K →ₙ+* A) (c : A ⊗[F] E →+* A ⊗[F] E) (ω : E) (m : ℕ) (r u : K)
    (hc1 : ∀ a : A, c (a ⊗ₜ 1) = a ⊗ₜ 1) (hcω : ∀ a : A, c (a ⊗ₜ ω) = a ⊗ₜ (1 - ω))
    (hω : ω * ω - ω + m = 0) (hr : r * r - r + m = 0) (hu : u * (1 - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ ω + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have h1 : e = j (φ u) * k ω - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * (1 - k ω) - j (φ u) * j (φ r) := by
    rw [he, map_add, hc1, hcω, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one, map_sub, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ (m : A ⊗[F] E) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - φ r + m * φ 1 = 0 := by
      rw [← nsmul_eq_mul, ← map_nsmul, ← map_mul, ← map_sub, ← map_add, nsmul_eq_mul, mul_one, hr, map_zero]
    simpa using congrArg j this
  · have : φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← map_mul, ← map_add, ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_ofNat] at h
  · have h := congrArg k hω
    rwa [map_add, map_sub, map_mul, map_natCast, map_zero] at h

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem evalV_singleV_same (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

def placeHom : Fv F v →ₙ+* AF F where
  toFun y := pairA F 0 (singleV F v y)
  map_zero' := Prod.ext rfl (af_ext F fun w => by
    change evalV F w (singleV F v 0) = evalV F w 0
    by_cases hw : w = v
    · subst hw; rw [evalV_singleV_same, map_zero]
    · rw [evalV_singleV_ne F v _ hw, map_zero])
  map_add' x y := Prod.ext (add_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x + y)) = evalV F w (singleV F v x + singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_add, evalV_singleV_same]
    · simp only [map_add, evalV_singleV_ne F v _ hw, add_zero])
  map_mul' x y := Prod.ext (mul_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x * y)) = evalV F w (singleV F v x * singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_mul, evalV_singleV_same]
    · simp only [map_mul, evalV_singleV_ne F v _ hw, mul_zero])

theorem singleV_mem_intAf (y : v.adicCompletionIntegers F) : singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne F v _ hw]; exact zero_mem _

theorem exists_root (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (k : ℕ) :
    ∃ r u : v.adicCompletionIntegers F, r * r - r + ((2 * k : ℕ) : v.adicCompletionIntegers F) = 0 ∧
      u * (1 - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (2 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← map_ofNat (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) 2, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h h2
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k : ℕ) : v.adicCompletionIntegers F)) (by monicity!) 0
    (by simpa using Ideal.mul_mem_right _ _ hm) (by simp)
  have hunit : IsUnit (1 - 2 * r) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right r _ hm)
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

end Local

theorem exists_omega (D : D7) : ∃ (ω : 𝓞 D.host.E) (k : ℕ),
    (ω : D.host.E) * ω - ω + ((2 * k : ℕ) : D.host.E) = 0 ∧ D.host.conj ω = 1 - ω := by
  obtain ⟨k, hm⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * (2 * k) := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  generalize hmm : 2 * k = m at hm
  set c : D.host.E := (1 + D.host.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : D.host.E) = 0 := by
    have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
    have hs := D.host.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, k, ?_, ?_⟩
  · show c * c - c + _ = 0
    rw [hmm, ← pow_two, hc]
  · show D.host.conj c = 1 - c
    simp only [c, map_div₀, map_add, map_one, D.host.conj_sqrtMinusD, map_ofNat]
    ring

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := D.host.conjE_apply _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem exists_split_idempotent : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : Formalism.L2.Theta.AE D, e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) ∧ ∃ α ∈ intAf D.host.F, ∃ β ∈ intAf D.host.F, ∃ ω : 𝓞 D.host.E, e = pairA D.host.F 0 α ⊗ₜ[D.host.F] (ω : D.host.E) + pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := by
  intro D v h2
  obtain ⟨ω, k, hω, hc⟩ := exists_omega D
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v h2 k
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  have key := idem_tensor (placeHom D.host.F v) (cA D) (ω : D.host.E) (2 * k) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun a => by rw [hcA, star_one]) (fun a => by rw [hcA, star_eq_conj, hc]) hω
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key.1, key.2.1, key.2.2, _, singleV_mem_intAf D.host.F v u, _,
    singleV_mem_intAf D.host.F v (-(u * r)), ω, rfl⟩

end GlobalTheory.SplitIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rational_points_completed_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  first | exact @GlobalTheory.CompletedLatticeFinite.finite_rational_points | exact GlobalTheory.CompletedLatticeFinite.finite_rational_points | (intros; apply GlobalTheory.CompletedLatticeFinite.finite_rational_points <;> assumption)
end

