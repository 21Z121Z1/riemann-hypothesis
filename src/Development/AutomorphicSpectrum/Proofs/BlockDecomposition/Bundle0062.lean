import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPowerSplit
section
open TensorProduct Module Function

namespace GlobalTheory.CompanionTheory.TopExtSplit

open GlobalTheory.TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

variable (R F) in

noncomputable def gradeProj (n : ℕ) : ExteriorAlgebra R F →ₗ[R] ⋀[R]^n F :=
  DirectSum.component R ℕ (fun k => ⋀[R]^k F) n ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun k : ℕ => ⋀[R]^k F)).toLinearMap

theorem gradeProj_same {n : ℕ} (x : ⋀[R]^n F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = x := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

theorem gradeProj_ne {m n : ℕ} (h : m ≠ n) (x : ⋀[R]^m F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = 0 := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = 0
  exact Subtype.ext (DirectSum.decompose_of_mem_ne _ x.2 h)

theorem exists_bigradedProj {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) :
    ∃ Ψ : ∀ a b : ℕ, ExteriorAlgebra R H →ₗ[R] (⋀[R]^a F) ⊗[R] (⋀[R]^b L),
      ∀ (a b a' b' : ℕ) (x : ⋀[R]^a' F) (y : ⋀[R]^b' L),
        Ψ a b (wedgeMap i s a' b' (x ⊗ₜ y) : ExteriorAlgebra R H) =
          gradeProj R F a (x : ExteriorAlgebra R F) ⊗ₜ
            gradeProj R L b (y : ExteriorAlgebra R L) := by
  let e : (0 : QuadraticForm R H) →qᵢ
      (QuadraticMap.prod (0 : QuadraticForm R F) (0 : QuadraticForm R L)) :=
    { r.prod π with map_app' := fun x => by simp }
  have he : ∀ x, e x = (r x, π x) := fun _ => rfl
  let Φ := (CliffordAlgebra.ofProd (0 : QuadraticForm R F) (0 : QuadraticForm R L)).comp
    (CliffordAlgebra.map e)
  have h₁ : Φ.comp (ExteriorAlgebra.map i) = GradedTensorProduct.includeLeft _ _ := by
    ext x
    simp [Φ, he, hri, hπi]
  have h₂ : Φ.comp (ExteriorAlgebra.map s) = GradedTensorProduct.includeRight _ _ := by
    ext x
    simp [Φ, he, hrs, hπs]
  refine ⟨fun a b => TensorProduct.map (gradeProj R F a) (gradeProj R L b) ∘ₗ
    (GradedTensorProduct.of R (CliffordAlgebra.evenOdd (0 : QuadraticForm R F))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R L))).symm.toLinearMap ∘ₗ Φ.toLinearMap, ?_⟩
  intro a b a' b' x y
  have hx := AlgHom.congr_fun h₁ x
  have hy := AlgHom.congr_fun h₂ y
  rw [AlgHom.comp_apply] at hx hy
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    coe_wedgeMap_tmul, map_mul, hx, hy, GradedTensorProduct.includeLeft_apply,
    GradedTensorProduct.includeRight_apply, GradedTensorProduct.tmul_one_mul_one_tmul]
  change TensorProduct.map (gradeProj R F a) (gradeProj R L b)
    ((x : ExteriorAlgebra R F) ⊗ₜ (y : ExteriorAlgebra R L)) = _
  rw [TensorProduct.map_tmul]

noncomputable def wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1)) :
    (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L) →ₗ[R] ⋀[R]^c H :=
  (LinearEquiv.ofEq _ _ (by rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.1 a.2)])).toLinearMap ∘ₗ
    wedgeMap i s a (c - a)

theorem coe_wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgePiece i s c a t : ExteriorAlgebra R H) = wedgeMap i s a (c - a) t := rfl

noncomputable def wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) :
    (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) →ₗ[R] ⋀[R]^c H :=
  LinearMap.lsum R _ ℕ (wedgePiece i s c)

theorem coe_wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ)
    (t : ∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgeSum i s c t : ExteriorAlgebra R H) =
      ∑ a : Fin (c + 1), (wedgeMap i s a (c - a) (t a) : ExteriorAlgebra R H) := by
  simp [wedgeSum, LinearMap.lsum_apply, coe_wedgePiece]

theorem wedgeSum_single (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    wedgeSum i s c (Pi.single a t) = wedgePiece i s c a t := by
  rw [wedgeSum, LinearMap.lsum_apply, LinearMap.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem wedgeSum_injective {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) (c : ℕ) : Injective (wedgeSum i s c) := by
  obtain ⟨Ψ, hΨ⟩ := exists_bigradedProj hri hrs hπi hπs
  have key : ∀ (a b a' b' : ℕ) (t : (⋀[R]^a F) ⊗[R] (⋀[R]^b L)),
      Ψ a' b' (wedgeMap i s a b t : ExteriorAlgebra R H) =
        TensorProduct.map (gradeProj R F a' ∘ₗ (⋀[R]^a F).subtype)
          (gradeProj R L b' ∘ₗ (⋀[R]^b L).subtype) t := by
    intro a b a' b' t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, Submodule.coe_add] at hx hy ⊢
      rw [hx, hy]
    | tmul x y =>
      rw [hΨ, TensorProduct.map_tmul]
      rfl
  have hl : ∀ t (a' : Fin (c + 1)),
      Ψ a' (c - a') (wedgeSum i s c t : ExteriorAlgebra R H) = t a' := by
    intro t a'
    rw [coe_wedgeSum, map_sum, Finset.sum_eq_single a']
    · rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a' : ℕ) F).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      have h₂ : gradeProj R L (c - a') ∘ₗ (⋀[R]^(c - a') L).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      rw [h₁, h₂, TensorProduct.map_id, LinearMap.id_apply]
    · intro a _ hne
      rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a : ℕ) F).subtype = 0 :=
        LinearMap.ext (gradeProj_ne (Fin.val_ne_of_ne hne))
      rw [h₁, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · simp
  intro t t' h
  funext a'
  rw [← hl t a', ← hl t' a', h]

theorem wedgeSum_surjective {i : F →ₗ[R] H} {s : L →ₗ[R] H}
    (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ) :
    Surjective (wedgeSum i s c) := by
  set A := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) with hA
  set B := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ s) with hB
  have hAB : LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) = A + B := by
    rw [hA, hB, LinearMap.range_comp, LinearMap.range_comp, Submodule.add_eq_sup,
      ← Submodule.map_sup, hsup, Submodule.map_top]
  have key : ∀ C D : Submodule R (ExteriorAlgebra R H),
      C ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) →
      D ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) → C * D ≤ D * C := by
    intro C D hC hD
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨u, rfl⟩ := hC hx
    obtain ⟨v, rfl⟩ := hD hy
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)
  have hA' : A ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_left
  have hB' : B ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_right
  have hc : Commute A B := le_antisymm (key _ _ hA' hB') (key _ _ hB' hA')
  obtain ⟨S, hS⟩ : ∃ S, S = (LinearMap.range (wedgeSum i s c)).map (⋀[R]^c H).subtype := ⟨_, rfl⟩
  have hpiece : ∀ k l, k + l = c → A ^ k * B ^ l ≤ S := by
    intro k l hkl
    obtain rfl : l = c - k := by omega
    have hk : k < c + 1 := by omega
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    rw [range_pow_eq_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hS]
    refine ⟨wedgeSum i s c (Pi.single (⟨k, hk⟩ : Fin (c + 1))
      ((⟨x, hx⟩ : ⋀[R]^k F) ⊗ₜ (⟨y, hy⟩ : ⋀[R]^(c - k) L))), ⟨_, rfl⟩, ?_⟩
    rw [wedgeSum_single, Submodule.subtype_apply, coe_wedgePiece]
    exact coe_wedgeMap_tmul _ _ _ _
  have hle : (⋀[R]^c H) ≤ S := by
    rw [ExteriorAlgebra.exteriorPower, hAB, hc.add_pow']
    refine Finset.sum_induction _ (· ≤ S) (fun x y hx hy => sup_le hx hy) bot_le ?_
    rintro ⟨k, l⟩ hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    have := hpiece k l hkl
    generalize c.choose (k, l).1 = n
    induction n with
    | zero => rw [zero_nsmul]; exact bot_le
    | succ n ih => rw [succ_nsmul]; exact sup_le ih this
  intro z
  have hz := hle z.2
  rw [hS] at hz
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hz
  exact ⟨t, Subtype.ext ht⟩

theorem ιMulti_cast {m n : ℕ} (h : n = m) (v : Fin m → H) :
    ExteriorAlgebra.ιMulti R m v = ExteriorAlgebra.ιMulti R n (v ∘ Fin.cast h) := by
  subst h
  rfl

theorem exteriorPower_split :
    ∀ (R F L H : Type) [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup L] [Module R L]
      [AddCommGroup H] [Module R H] (i : F →ₗ[R] H) (s : L →ₗ[R] H) (r : H →ₗ[R] F)
      (π : H →ₗ[R] L) (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0)
      (hπi : ∀ x, π (i x) = 0) (hπs : ∀ y, π (s y) = y)
      (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ),
      ∃ e : (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) ≃ₗ[R] ⋀[R]^c H,
        ∀ (a : Fin (c + 1)) (f : Fin a → F) (h : Fin (c - a) → L),
          e (Pi.single a (exteriorPower.ιMulti R a f ⊗ₜ exteriorPower.ιMulti R (c - a) h)) =
            exteriorPower.ιMulti R c
              (Fin.append (fun k => i (f k)) (fun k => s (h k)) ∘
                Fin.cast (by have := a.2; omega)) := by
  intro R F L H _ _ _ _ _ _ _ i s r π hri hrs hπi hπs hsup c
  refine ⟨LinearEquiv.ofBijective (wedgeSum i s c)
    ⟨wedgeSum_injective hri hrs hπi hπs c, wedgeSum_surjective hsup c⟩, fun a f h =>
      Subtype.ext ?_⟩
  change (wedgeSum i s c _ : ExteriorAlgebra R H) = _
  rw [wedgeSum_single, coe_wedgePiece, coe_wedgeMap_tmul]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact ιMulti_cast _ _

end GlobalTheory.CompanionTheory.TopExtSplit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ExtTensorFixed

variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

theorem coord_lTensor (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hx, hy]
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

theorem mem_range_lTensor_fixed (σ : Representation ℂ G W) (K : Subgroup G) (y : X ⊗[ℂ] W)
    (hy : ∀ k : K, (σ (k : G)).lTensor X y = y) :
    y ∈ LinearMap.range ((fixed σ K).subtype.lTensor X) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ X
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have hc : ∀ i, e y i ∈ fixed σ K := fun i => (mem_fixed_iff σ K _).2 fun k => by
    have h := coord_lTensor b (σ (k : G)) y i
    rw [hy k] at h
    exact h.symm
  have hy' : y = (e y).sum fun i n => b i ⊗ₜ[ℂ] n := by
    have h : e.symm (e y) = _ := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e y)
    exact (e.symm_apply_apply y).symm.trans h
  rw [hy']
  refine Submodule.sum_mem _ fun i _ => ⟨b i ⊗ₜ[ℂ] (⟨e y i, hc i⟩ : fixed σ K), ?_⟩
  simp

theorem fixed_le_range (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (K₁ : Subgroup G) (K₂ : Subgroup H) :
    fixed (extTensor ρ σ) (K₁.prod K₂) ≤
      LinearMap.range (TensorProduct.map (fixed ρ K₁).subtype (fixed σ K₂).subtype) := by
  intro x hx
  have hx' := (mem_fixed_iff _ _ _).1 hx
  have act : ∀ (g : G × H) (z : V ⊗[ℂ] W),
      extTensor ρ σ g z = TensorProduct.map (ρ g.1) (σ g.2) z := by
    intro g z
    induction z with
    | zero => simp
    | add a c ha hc => simp [ha, hc]
    | tmul v w => simp

  have h1 : ∀ k : K₁, (ρ (k : G)).lTensor W (TensorProduct.comm ℂ V W x) =
      TensorProduct.comm ℂ V W x := by
    intro k
    have hk := hx' ⟨((k : G), 1), ⟨k.2, one_mem _⟩⟩
    rw [act] at hk
    conv_rhs => rw [← hk]
    simp only [map_one]
    generalize x = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨y', hy'⟩ := mem_range_lTensor_fixed ρ K₁ _ h1
  let y : (fixed ρ K₁) ⊗[ℂ] W := TensorProduct.comm ℂ W (fixed ρ K₁) y'
  have hy : (fixed ρ K₁).subtype.rTensor W y = x := by
    have : (fixed ρ K₁).subtype.rTensor W y =
        TensorProduct.comm ℂ W V ((fixed ρ K₁).subtype.lTensor W y') := by
      simp only [y]
      generalize y' = z
      induction z with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul v w => simp
    rw [this, hy']
    simp

  have hinj : Function.Injective ((fixed ρ K₁).subtype.rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have h2 : ∀ k : K₂, (σ (k : H)).lTensor (fixed ρ K₁) y = y := by
    intro k
    apply hinj
    have hk := hx' ⟨(1, (k : H)), ⟨one_mem _, k.2⟩⟩
    rw [act] at hk
    rw [hy]
    conv_rhs => rw [← hk, ← hy]
    simp only [map_one]
    generalize y = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨z, hz⟩ := mem_range_lTensor_fixed σ K₂ y h2
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  generalize z = t
  induction t with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v w => simp

theorem finiteDimensional_fixed_extTensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H),
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) →
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  intro G H V W _ _ _ _ _ _ ρ σ K₁ K₂ h₁ h₂
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ σ K₁ K₂)

end GlobalTheory.CompanionTheory.ExtTensorFixed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotient
section
namespace GlobalTheory.CompanionTheory.ProdQuotient

theorem support_mul_out_finite (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  let φ : (G₁ × G₂) ⧸ K₁.prod K₂ → (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    fun q => ((q.out.1 : G₁ ⧸ K₁), (q.out.2 : G₂ ⧸ K₂))
  have hinj : Function.Injective φ := by
    intro a b hab
    have e₁ : ((a.out.1 : G₁ ⧸ K₁)) = (b.out.1 : G₁ ⧸ K₁) := congrArg Prod.fst hab
    have e₂ : ((a.out.2 : G₂ ⧸ K₂)) = (b.out.2 : G₂ ⧸ K₂) := congrArg Prod.snd hab
    rw [QuotientGroup.eq] at e₁ e₂
    have key : ((a.out : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂) = (b.out : G₁ × G₂) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.mpr ⟨e₁, e₂⟩
    simpa using key
  have inv₁ : ∀ g : G₁, f₁ (g : G₁ ⧸ K₁).out = f₁ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
    rw [hk]
    exact i₁ k k.2 g
  have inv₂ : ∀ g : G₂, f₂ (g : G₂ ⧸ K₂).out = f₂ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₂ g
    rw [hk]
    exact i₂ k k.2 g
  refine ((h₁.prod h₂).preimage hinj.injOn).subset ?_
  intro q hq
  have hq' : f₁ q.out.1 * f₂ q.out.2 ≠ 0 := hq
  refine ⟨?_, ?_⟩
  · change f₁ (q.out.1 : G₁ ⧸ K₁).out ≠ 0
    rw [inv₁]
    exact left_ne_zero_of_mul hq'
  · change f₂ (q.out.2 : G₂ ⧸ K₂).out ≠ 0
    rw [inv₂]
    exact right_ne_zero_of_mul hq'

end GlobalTheory.CompanionTheory.ProdQuotient
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumCosetSmulLinear
section
namespace GlobalTheory.CompanionTheory.HeckeSum

theorem finsum_coset_smul_linear :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (J : Type) [Fintype J] (c : J → ℂ) (f : J → G → ℂ),
      (∀ j, (Function.support fun q : G ⧸ K => f j q.out).Finite) → ∀ v : V,
      ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
        = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
  intro G V _ _ _ ρ K J _ c f hf v
  have hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite := by
    intro j
    refine (hf j).subset ?_
    intro q hq h0
    apply hq
    show f j q.out • ρ q.out v = 0
    have h0' : f j q.out = 0 := h0
    rw [h0', zero_smul]
  have hs' : ∀ j ∈ (Finset.univ : Finset J),
      (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite := by
    intro j _
    refine (hs j).subset ?_
    intro q hq h0
    apply hq
    show c j • (f j q.out • ρ q.out v) = 0
    have h0' : f j q.out • ρ q.out v = 0 := h0
    rw [h0', smul_zero]
  calc ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
      = ∑ᶠ q : G ⧸ K, ∑ j, c j • (f j q.out • ρ q.out v) := by
        refine finsum_congr fun q => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) :=
        finsum_sum_comm _ _ hs'
    _ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_finsum' (c j) (hs j)]

end GlobalTheory.CompanionTheory.HeckeSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
section
noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicativeStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_schmidt_norm_submultiplicative : ∀ {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ), Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | exact GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | (intros; apply GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBoundStatement
section
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ → (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) → ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ) → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) → ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧ ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧ Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧ ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | exact GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | (intros; apply GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main <;> assumption)
end

