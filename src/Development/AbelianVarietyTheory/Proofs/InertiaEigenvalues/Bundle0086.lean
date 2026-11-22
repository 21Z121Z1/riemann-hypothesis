import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomSubmoduleFgAndSpanEqTop
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem exists_smul_mem_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E]
    [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (a : A) :
    ∃ d ∈ nonZeroDivisors O, d • a ∈ M := by
  have ha : a ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₂ * d₁, mul_mem hd₂ hd₁, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm d₂ d₁ y]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  | smul e x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨o, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have h1 : (s : O) • (e • x) = o • x := by
      rw [← algebraMap_smul E (s : O) (e • x), smul_smul, mul_comm, hs, algebraMap_smul]
    refine ⟨(s : O) * d, mul_mem s.2 hd, ?_⟩
    rw [mul_comm, mul_smul, h1, smul_comm d o x]
    exact M.smul_mem o h

theorem exists_smul_mem_finset_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E]
    [Algebra O E] [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A]
    [IsScalarTower O E A] (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (t : Finset A) :
    ∃ d ∈ nonZeroDivisors O, ∀ a ∈ t, d • a ∈ M := by
  classical
  refine Finset.induction_on t ⟨1, one_mem _, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨d₁, hd₁, h₁⟩ := ih
  obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_span_eq_top O E M hM a
  refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mul_smul]; exact M.smul_mem _ h₂
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ (h₁ b hb)

theorem homLat_fg_and_span_eq_top (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁]
    [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂]
    [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) :
    IsLat O E M₁ → IsLat O E M₂ →
      (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  classical
  intro h₁ h₂
  obtain ⟨h₁fg, h₁sp⟩ := h₁
  obtain ⟨h₂fg, h₂sp⟩ := h₂
  obtain ⟨s, hs⟩ := h₂fg
  have hsE : Submodule.span E (s : Set A₂) = ⊤ := by
    rw [eq_top_iff, ← h₂sp, Submodule.span_le, ← hs]
    exact fun x hx => Submodule.span_le_restrictScalars O E _ hx
  have memH : ∀ ψ ∈ homLat E M₁ M₂, ∀ x ∈ M₂, ψ x ∈ M₁ := fun ψ hψ => hψ
  refine ⟨?_, ?_⟩
  · haveI : Module.Finite O M₁ := Module.Finite.iff_fg.mpr h₁fg
    let f : homLat E M₁ M₂ →ₗ[O] (s → M₁) :=
      { toFun := fun ψ x => ⟨ψ.1 x, memH ψ.1 ψ.2 x (hs ▸ Submodule.subset_span x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro ψ φ h
      apply Subtype.ext
      apply LinearMap.ext_on hsE
      intro x hx
      exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
    haveI := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp this
  · rw [eq_top_iff]
    intro ψ _
    obtain ⟨d, hd, hdψ⟩ := exists_smul_mem_finset_of_span_eq_top O E M₁ h₁sp (s.image ψ)
    have hmem : d • ψ ∈ homLat E M₁ M₂ := by
      show ∀ x ∈ M₂, (d • ψ) x ∈ M₁
      intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => rw [LinearMap.smul_apply]; exact hdψ _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact M₁.add_mem hy hz
      | smul o y _ hy => rw [LinearMap.map_smul_of_tower]; exact M₁.smul_mem o hy
    have hd' : algebraMap O E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hψ : ψ = (algebraMap O E d)⁻¹ • (d • ψ) := by
      rw [← algebraMap_smul E d ψ, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)

def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)

def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom

def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val

def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem bas_apply (hG : A.IsGen τ p) (i : Fin r) : LinDesc.bas A hG i = τ ^ (i : ℕ) := by
  simp [LinDesc.bas]

theorem repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by
  have : (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]; simp [bas_apply]
  rw [this]
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp

theorem leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj]
    have h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ) := by
      have := hG.2.2
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left this
    rw [h3, repr_sum]; simp
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    have h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩ := by rw [bas_apply]
    rw [h3, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg]
      intro h; exact hi (by rw [← h])

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := rfl

theorem tm_inv_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl

theorem row_mul (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by
        rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf

theorem act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by
  unfold act pt
  rw [tm_inv_coe, tm_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← leftMul_tau A hG, ← map_mul, ← map_mul]; congr 1
    rw [mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · simp only
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr _ _ _
  · exact row_mul A hG _ c

theorem det_tm (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = Algebra.norm F (t : A.K) := by
  rw [tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem act_one {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
theorem pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactModuleTopology
section
open Polynomial TensorProduct

noncomputable section

namespace GlobalTheory.JR.EtExist

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def conjAlg [h : Unram F E] : E →ₐ[F] E :=
  { starRingEnd E with commutes' := fun x => h.star_fix x }

theorem conjAlg_apply [Unram F E] (y : E) : conjAlg F E y = star y := rfl

variable (K : Type) [CommRing K] [Algebra F K]

def conjT [Unram F E] : E ⊗[F] K →ₐ[F] E ⊗[F] K := Algebra.TensorProduct.map (conjAlg F E) (AlgHom.id F K)

theorem conjT_conjT [Unram F E] (z : E ⊗[F] K) : conjT F E K (conjT F E K z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjT, conjAlg_apply]
  | add a b ha hb => simp [ha, hb]

@[reducible] def starT [Unram F E] : StarRing (E ⊗[F] K) where
  star := conjT F E K
  star_involutive := conjT_conjT F E K
  star_mul a b := by
    change conjT F E K (a * b) = conjT F E K b * conjT F E K a
    rw [map_mul, mul_comm]
  star_add a b := map_add (conjT F E K) a b

theorem locallyCompact_moduleTopology [LocallyCompactSpace F] [Module.Finite F K] :
    @LocallyCompactSpace K (moduleTopology F K) := by
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  let b := (Module.finBasis F K).equivFun
  have h1 : Continuous b := IsModuleTopology.continuous_of_linearMap b.toLinearMap
  haveI : ContinuousAdd K := IsModuleTopology.toContinuousAdd F K
  have h2 : Continuous b.symm := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  let e : K ≃ₜ (Fin (Module.finrank F K) → F) := { b.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  exact e.isClosedEmbedding.locallyCompactSpace

def ofAlgebra [h : Unram F E] [Module.Finite F K] [IsReduced K] : Et F E :=
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[F] K) := moduleTopology F (E ⊗[F] K)
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  { K := K
    L := E ⊗[F] K
    trK := IsModuleTopology.isTopologicalRing F K
    lcK := haveI := h.lcF; locallyCompact_moduleTopology F K
    mK := borel K
    bK := @BorelSpace.mk _ _ (borel K) rfl
    stL := starT F E K
    mtL := ⟨rfl⟩
    mL := borel (E ⊗[F] K)
    bL := @BorelSpace.mk _ _ (borel (E ⊗[F] K)) rfl
    push := inferInstance
    star_K := fun x => by
      change conjT F E K (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [conjT]
    star_E := fun y => by
      change conjT F E K (y ⊗ₜ 1) = star y ⊗ₜ 1
      simp [conjT, conjAlg_apply] }

theorem exists_field [h : Unram F E] : ∃ A : Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1 := by
  haveI := h.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.finrank_eq]; norm_num)
  exact ⟨{ K := F, L := E, mK := borel F, bK := @BorelSpace.mk _ _ (borel F) rfl, mL := borel E,
           bL := @BorelSpace.mk _ _ (borel E) rfl, mtL := isModuleTopologyOfFiniteDimensional,
           push := inferInstance, star_K := h.star_fix, star_E := fun _ => rfl },
    Field.toIsField F, Field.toIsField E, Module.finrank_self F⟩

theorem exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  set P : F[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : F[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite F (AdjoinRoot P) := pb.finite
  haveI : IsReduced (AdjoinRoot P) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      ((isRadical_iff_span_singleton).1 hs.squarefree.isRadical)
  refine ⟨ofAlgebra F E (AdjoinRoot P), AdjoinRoot.root P, ?_, ?_, ?_⟩
  · change LinearIndependent F (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ))
    have := pb.basis.linearIndependent.comp (Fin.cast (show r = pb.dim from hd.symm)) (Fin.cast_injective _)
    have e : (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ)) = pb.basis ∘ Fin.cast (show r = pb.dim from hd.symm) := by
      funext i
      rw [Function.comp_apply, pb.basis_eq_pow]
      rfl
    rw [e]; exact this
  · change Module.finrank F (AdjoinRoot P) = r
    rw [pb.finrank]; exact hd
  · change AdjoinRoot.root P ^ r + ∑ i, p i • AdjoinRoot.root P ^ (i : ℕ) = 0
    have := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at this
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]) = 0 := this
    simp only [map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    simpa only [Algebra.smul_def] using h2

theorem exists_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [GlobalTheory.JR.Unram F E],
    (∃ A : GlobalTheory.JR.Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1) ∧
    ∀ (r : ℕ) (p : Fin r → F),
      (Polynomial.X ^ r + ∑ i, Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) : Polynomial F).Separable →
      ∃ (A : GlobalTheory.JR.Et F E) (τ : A.K), A.IsGen τ p :=
  fun F E _ _ _ _ _ => ⟨exists_field F E, exists_isGen F E⟩

end GlobalTheory.JR.EtExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApply
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem slices_test {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P]
    [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ) (hT : ∀ φ, IsTest φ → IsTest (T φ)) (hT0 : T 0 = 0)
    (f : P × V × Q → ℂ) (hf : IsTest f) :
    (∀ p q, IsTest (fun v => f (p, v, q))) ∧
      IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hC : IsCompact (tsupport f) := hcs
  have hz : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ p q, IsTest (fun v => f (p, v, q)) := by
    intro p q
    refine ⟨hlc.comp_continuous (by fun_prop), ?_⟩
    have hcl : IsClosed ({x : P × V × Q | x.1 = p} ∩ {x | x.2.2 = q}) :=
      (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)
    refine HasCompactSupport.intro ((hC.inter_right hcl).image (continuous_fst.comp continuous_snd)) ?_
    intro v hv
    apply hz
    intro hmem
    exact hv ⟨(p, v, q), ⟨hmem, rfl, rfl⟩, rfl⟩
  refine ⟨h1, ?_⟩
  set Φ : P × Q → V → ℂ := fun a v => f (a.1, v, a.2) with hΦdef
  set CV : Set V := (fun x : P × V × Q => x.2.1) '' tsupport f with hCV
  have hCVc : IsCompact CV := hC.image (continuous_fst.comp continuous_snd)
  have hoff : ∀ (a : P × Q) v, v ∉ CV → f (a.1, v, a.2) = 0 := by
    intro a v hv
    exact hz _ (fun h => hv ⟨_, h, rfl⟩)
  have hΦ : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a0
    have hn : IsOpen {z : (P × Q) × V | f (z.1.1, z.2, z.1.2) = f (a0.1, z.2, a0.2)} := by
      have g1 : IsLocallyConstant (fun z : (P × Q) × V => f (z.1.1, z.2, z.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have g2 : IsLocallyConstant (fun z : (P × Q) × V => f (a0.1, z.2, a0.2)) :=
        hlc.comp_continuous (by fun_prop)
      refine isOpen_iff_mem_nhds.2 fun z hz' => ?_
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 g1 z, (IsLocallyConstant.iff_eventually_eq _).1 g2 z]
        with y hy1 hy2
      show f (y.1.1, y.2, y.1.2) = f (a0.1, y.2, a0.2)
      rw [hy1, hy2]
      exact hz'
    obtain ⟨u, w, hu, -, hau, hCVw, huw⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := a0)) hCVc hn (by
        rintro ⟨a, v⟩ ⟨ha, -⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl)
    filter_upwards [hu.mem_nhds (hau rfl)] with a ha
    funext v
    by_cases hv : v ∈ CV
    · exact huw (show (a, v) ∈ u ×ˢ w from ⟨ha, hCVw hv⟩)
    · show f (a.1, v, a.2) = f (a0.1, v, a0.2)
      rw [hoff a v hv, hoff a0 v hv]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x0
    have e1 : ∀ᶠ x in 𝓝 x0, Φ (x.1, x.2.2) = Φ (x0.1, x0.2.2) :=
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 hΦ _)
    have e2 : ∀ᶠ x in 𝓝 x0, T (Φ (x0.1, x0.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 (hT _ (h1 _ _)).1 _)
    filter_upwards [e1, e2] with x h h'
    show T (Φ (x.1, x.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1
    rw [h]
    exact h'
  · set K : Set (P × Q) := (fun x : P × V × Q => (x.1, x.2.2)) '' tsupport f with hKdef
    have hK : IsCompact K := hC.image (by fun_prop)
    have hΦK : ∀ a, a ∉ K → Φ a = 0 := by
      intro a ha
      funext v
      exact hz _ (fun h => ha ⟨_, h, rfl⟩)
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hfin : (Set.range (fun a : K => Φ a)).Finite :=
      (hΦ.comp_continuous continuous_subtype_val).range_finite
    set U : Set V := ⋃ h ∈ Set.range (fun a : K => Φ a), tsupport (T h) with hUdef
    have hU : IsCompact U := hfin.isCompact_biUnion (fun h hh => by
      obtain ⟨a, rfl⟩ := hh
      exact (hT _ (h1 _ _)).2.isCompact)
    have hL : IsCompact ((fun z : (P × Q) × V => (z.1.1, z.2, z.1.2)) '' (K ×ˢ U)) :=
      (hK.prod hU).image (by fun_prop)
    refine HasCompactSupport.intro hL ?_
    intro x hx
    by_contra hne
    apply hx
    have ha : (x.1, x.2.2) ∈ K := by
      by_contra hK'
      apply hne
      show T (Φ (x.1, x.2.2)) x.2.1 = 0
      rw [hΦK _ hK', hT0]
      rfl
    refine ⟨((x.1, x.2.2), x.2.1), ⟨ha, ?_⟩, rfl⟩
    exact Set.mem_biUnion ⟨⟨(x.1, x.2.2), ha⟩, rfl⟩ (subset_tsupport _ hne)

theorem slices_test' : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) :=
  fun T hT hT0 f hf => slices_test T hT hT0 f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInvLSIffTendsto
section
open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

theorem mem_invL_S_iff_tendsto (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] (f : K⟦X⟧) :
    f ∈ invL l (S O K e) ↔ Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  have key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n =
      ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n) := fun m n => by
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  constructor
  · rintro ⟨m, hm⟩
    have h := (mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [key, inv_mul_cancel_left₀ (pow_pos hl m).ne']
  · intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove_range
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩
    · rw [key]
      exact (mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le
    · have h3 := hf.const_mul (‖(l : K)‖ ^ m)
      rw [mul_zero] at h3
      exact h3.congr fun n => (key m n).symm

end GlobalTheory.BK
end

