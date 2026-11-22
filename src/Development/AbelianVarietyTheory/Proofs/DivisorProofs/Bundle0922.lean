import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebras
section
open GlobalTheory.EtC

namespace GlobalTheory.QUnits

theorem tensorFractionRing_units_pow_surj : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ u
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let R := TensorProduct T (FractionRing T) A
  let f : O →+* R := (Algebra.TensorProduct.includeRight : A →ₐ[T] R).toRingHom.comp π.toRingHom
  have hπT : ∀ t : T, π (algebraMap T O t) = algebraMap T A t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hfT : ∀ t : T, f (algebraMap T O t) = algebraMap T R t := by
    intro t
    change Algebra.TensorProduct.includeRight (π (algebraMap T O t)) = _
    rw [hπT, AlgHom.commutes]
  have hf : ∀ y : Algebra.algebraMapSubmonoid O (nonZeroDivisors T), IsUnit (f y) := by
    rintro ⟨_, t, ht, rfl⟩
    change IsUnit (f (algebraMap T O t))
    rw [hfT, IsScalarTower.algebraMap_apply T (FractionRing T) R]
    exact (IsLocalization.map_units (FractionRing T) ⟨t, ht⟩).map _
  let φ : L →+* R := IsLocalization.lift hf
  have hφ : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero φ⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add φ a b⟩
    | tmul k a =>
      obtain ⟨o, rfl⟩ := hπ a
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) k
      refine ⟨IsLocalization.mk' L (algebraMap T O x * o)
        (⟨algebraMap T O s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ :
          Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ?_⟩
      rw [IsLocalization.lift_mk'_spec]
      change f (algebraMap T O x * o) = f (algebraMap T O (s : T)) * _
      rw [map_mul, hfT, hfT]
      change algebraMap T R x * (Algebra.TensorProduct.includeRight (π o)) = _
      have hR : ∀ t : T, algebraMap T R t = algebraMap T (FractionRing T) t ⊗ₜ[T] (1 : A) := fun t => rfl
      rw [Algebra.TensorProduct.includeRight_apply, hR, hR, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, IsLocalization.mk'_spec']
  have hB : ∀ P : Ideal L, P.IsPrime → P ≠ ⊥ → P.IsMaximal ∧ ∀ x : L, ∃ c d : T, d ≠ 0 ∧
      algebraMap T L d * x - algebraMap T L c ∈ P := by
    intro P hP hne
    obtain ⟨g, hg, hgP⟩ := GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization T hAIC O hind P hP hne
    exact GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image T hAIC O hind P hP g hg hgP
  by_cases hJ : RingHom.ker φ = ⊥
  · have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hJ
    let e : L ≃+* R := RingEquiv.ofBijective φ ⟨hinj, hφ⟩
    obtain ⟨v, hv⟩ := GlobalTheory.LocAcycUnits.units_localization_pow_surj T O q ⟨inferInstance, hAIC⟩ hq hq0
      hind (Units.map e.symm.toMonoidHom u)
    refine ⟨Units.map e.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]; ext; simp
  · let J := RingHom.ker φ
    let e : L ⧸ J ≃+* R := RingHom.quotientKerEquivOfSurjective hφ
    have hne : ∀ I : Ideal (L ⧸ J), I.comap (Ideal.Quotient.mk J) ≠ ⊥ := by
      intro I h
      apply hJ
      rw [eq_bot_iff]
      intro x hx
      rw [← h, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact I.zero_mem
    haveI : Ring.KrullDimLE 0 (L ⧸ J) := by
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have hP : (I.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      have hmax := (hB _ hP (hne I)).1
      have := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hmax
      rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at this
      exact this.resolve_left hI.ne_top
    have hqL : IsUnit (q : L ⧸ J) := by
      have := hq.map (algebraMap T (L ⧸ J)); simpa using this
    have hroot : ∀ m : Ideal (L ⧸ J), m.IsMaximal → ∃ x : L ⧸ J,
        x ^ q - ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J) ∈ m := by
      intro m hm
      obtain ⟨w0, hw0⟩ := Ideal.Quotient.mk_surjective
        ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J)
      have hP : (m.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨c, d, hd, hcd⟩ := (hB _ hP (hne m)).2 w0
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hAIC (Polynomial.X ^ (n + 1) - Polynomial.C (c * d ^ n))
        (Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero n))
        (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hq0)
      have hrq : r ^ (n + 1) = c * d ^ n := by simpa [sub_eq_zero] using hr
      have hdu : IsUnit (algebraMap T L d) := by
        rw [IsScalarTower.algebraMap_apply T O L]
        exact IsLocalization.map_units L (⟨algebraMap T O d,
          Algebra.mem_algebraMapSubmonoid_of_mem (⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ :
            nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      set D := algebraMap T L d
      set Dinv : L := ((hdu.unit⁻¹ : Lˣ) : L)
      have hDn : Dinv ^ (n + 1) * D ^ (n + 1) = 1 := by
        rw [← mul_pow, IsUnit.val_inv_mul, one_pow]
      have hR : algebraMap T L r ^ (n + 1) = algebraMap T L c * D ^ n := by
        rw [← map_pow, hrq, map_mul, map_pow]
      refine ⟨Ideal.Quotient.mk J (algebraMap T L r * Dinv), ?_⟩
      rw [← hw0, ← map_pow, ← map_sub, ← Ideal.mem_comap]
      have key : (algebraMap T L r * Dinv) ^ (n + 1) - w0 =
          -(Dinv ^ (n + 1) * D ^ n) * (D * w0 - algebraMap T L c) := by
        linear_combination Dinv ^ (n + 1) * hR + w0 * hDn
      rw [key]
      exact Ideal.mul_mem_left _ _ hcd
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_root_of_unit_zero_dimensional (L ⧸ J) q hq0 hqL (Units.map e.symm.toMonoidHom u) hroot
    exact ⟨Units.map e.toMonoidHom v, by rw [← map_pow, hv]; ext; simp⟩

end GlobalTheory.QUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.RealCoord

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def perL (X : Data E r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ × Fin r → ℂ) where
  toFun := perC X x
  map_add' u v := by
    funext p
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    · rw [Matrix.mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext p
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Matrix.mulVec_smul, Pi.smul_apply]

theorem hermC_col_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (c : Fin r → ℂ) : hermC τ G (FD.col x a) (x *ᵥ c) = ∑ b, FD.gram τ G x a b * conj (c b) := by
  simp only [hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem perL_injective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Injective (perL X x) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  funext τ
  have hd : (mat x τ).det ≠ 0 := (hx τ).1
  have hA : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have e : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl
    rw [e, h0] at h
    simp at h
  set c : Fin r → ℂ := (mat x τ)⁻¹ *ᵥ u τ with hc
  have hu' : u τ = mat x τ *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]
  have h2 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    have := congrFun hu (τ, a)
    change perC X x u (τ, a) = 0 at this
    simpa only [perC, if_neg ha] using this
  have h1 : X.gramPos x τ *ᵥ (fun b => conj (c (Fin.castLE X.p0_le b))) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := a.2
    have := congrFun hu (τ, Fin.castLE X.p0_le a)
    change perC X x u (τ, Fin.castLE X.p0_le a) = 0 at this
    simp only [perC, if_pos ha] at this
    rw [hu', hermC_col_mulVec] at this
    rw [Pi.zero_apply, ← this]
    simp only [Matrix.mulVec, dotProduct, Data.gramPos, Matrix.submatrix_apply]
    refine Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _ (fun b hb => ?_) fun _ => rfl
    rw [h2 b fun h => hb ⟨⟨b, h⟩, rfl⟩, map_zero, mul_zero]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hA h1
  have h4 : c = 0 := by
    funext a
    by_cases ha : (a : ℕ) < X.p0
    · have := congrFun h3 ⟨a, ha⟩
      simpa using this
    · exact h2 a ha
  rw [hu', h4, Matrix.mulVec_zero]
  rfl

theorem perL_bijective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Bijective (perL X x) := by
  refine ⟨perL_injective X hx, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (perL_injective X hx)
  simp [Module.finrank_pi_fintype, mul_assoc]

end Lin

variable {D : D7}

theorem realM_tauE (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.PointAtPlace.tauE_injective h.choose_spec]

theorem realM_add (θ : InfFam D) {m n : ℕ} (v w : Mx D m n) (τ : D.host.E →+* ℂ) :
    realM θ (v + w) τ = realM θ v τ + realM θ w τ := by
  unfold realM
  split_ifs with h
  · funext i j
    show θ _ (infPart D (v i j + w i j)) = θ _ (infPart D (v i j)) + θ _ (infPart D (w i j))
    rw [RingHom.map_add, RingHom.map_add]
  · rw [add_zero]

theorem continuous_realM {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.host.E →+* ℂ) (i : Fin m) (j : Fin n) :
    Continuous fun w : Mx D m n => realM θ w τ i j := by
  unfold realM
  split_ifs with h
  · exact (GlobalTheory.FockCompare.continuous_comp hθ _).comp ((continuous_apply j).comp (continuous_apply i))
  · exact continuous_const

theorem realM_lineAt {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (ρ : D.what₂.Tau) (u : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (τ : D.host.E →+* ℂ) : realM θ (lineAt θ ρ u t) τ = t • realM θ (lineAt θ ρ u 1) τ := by
  have hL : IsLineAt θ ρ u (lineAt θ ρ u) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n ρ u)
  unfold realM
  split_ifs with h
  · rw [hL.2.2, hL.2.2]
    split_ifs
    · funext i j
      simp
    · rw [smul_zero]
  · rw [smul_zero]

theorem zOf_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (v : WO V W), v.map (infPart D) = (ratW W V γ).map (infPart D) → zOf θ V W hr X idx x v = fun b => pv X idx x (colsR hr γ b)) ∧ (∀ v w : WO V W, zOf θ V W hr X idx x (v + w) = zOf θ V W hr X idx x v + zOf θ V W hr X idx x w) ∧ (∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) (t : ℝ), zOf θ V W hr X idx x (lineAt θ τ u t) = (t : ℂ) • zOf θ V W hr X idx x (lineAt θ τ u 1)) ∧ Continuous (zOf θ V W hr X idx x ) ∧ (x ∈ X.dom → ∃ p : (Fin V.rank → Fin g → ℂ) →+ WO V W, Continuous p ∧ (∀ z, (p z).map (finPart D) = 0 ∧ zOf θ V W hr X idx x (p z) = z) ∧ ∀ w : WO V W, w.map (finPart D) = 0 → p (zOf θ V W hr X idx x w) = w) := by
  intro D ψ θ V W r g hr X bas idx _ hθ _ _ hM _ x
  have hz : ∀ w b j, zOf θ V W hr X idx x w b j =
      perL X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j) := fun _ _ _ => rfl
  refine ⟨fun γ v hv => ?_, fun v w => ?_, fun ρ u t => ?_, ?_, fun hx => ?_⟩
  · funext b j
    show perC X x _ (idx j) = per X x _ (idx j)
    rw [← perC_emb]
    congr 1
    funext τ a
    obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
    have e : infPart D (v (Fin.cast hr.symm a) b) = infPart D (incA D (γ (Fin.cast hr.symm a) b)) :=
      congrFun (congrFun hv _) _
    show realM θ v τ.1 _ _ = τ.1 (γ (Fin.cast hr.symm a) b)
    rw [hρ, realM_tauE, ← GlobalTheory.FockCompare.comp_incA hθ, ← e]
    rfl
  · funext b j
    rw [Pi.add_apply, Pi.add_apply, hz, hz, hz, ← Pi.add_apply (perL X x _), ← map_add]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_add]
    rfl
  · funext b j
    rw [Pi.smul_apply, Pi.smul_apply, hz, hz, Complex.coe_smul, ← Pi.smul_apply t (perL X x _), ← map_smul]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_lineAt hθ]
    rfl
  · refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [hz]
    exact (continuous_apply (idx j)).comp ((perL X x).continuous_of_finiteDimensional.comp
      (continuous_pi fun τ => continuous_pi fun a => continuous_realM hθ τ.1 _ b))
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L := LinearEquiv.ofBijective (perL X x) (perL_bijective X hx)
    have hL : ∀ u, L u = perL X x u := fun _ => rfl
    let pl : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    let p : (Fin V.rank → Fin g → ℂ) →+ WO V W :=
      { toFun := fun z => Matrix.of fun i b => σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i)
        map_zero' := by
          funext i b
          have : (fun q => (0 : Fin V.rank → Fin g → ℂ) b (idx.symm q)) = 0 := rfl
          rw [Matrix.of_apply, this, map_zero]
          exact σ.map_zero
        map_add' := fun z z' => by
          funext i b
          have : (fun q => (z + z') b (idx.symm q)) = (fun q => z b (idx.symm q)) + fun q => z' b (idx.symm q) := rfl
          rw [Matrix.of_apply, this, map_add]
          exact σ.map_add _ _ }
    have hp : ∀ z i b, p z i b = σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i) :=
      fun _ _ _ => rfl
    refine ⟨p, ?_, fun z => ⟨?_, ?_⟩, fun w hw => ?_⟩
    · refine continuous_pi fun i => continuous_pi fun b => hσ.cont.comp (continuous_pi fun ρ => ?_)
      exact (continuous_apply (Fin.cast hr i)).comp ((continuous_apply (pl ρ)).comp
        (L.symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_pi fun q => (continuous_apply (idx.symm q)).comp (continuous_apply b))))
    · funext i b
      exact hσ.fin _
    · funext b j
      have e : (fun (τ : X.Ψ) a => realM θ (p z) τ.1 (Fin.cast hr.symm a) b) =
          L.symm (fun q => z b (idx.symm q)) := by
        funext τ a
        obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
        obtain rfl : τ = pl ρ := Subtype.ext hρ
        show realM θ (p z) (tauE D ρ) _ _ = _
        rw [realM_tauE]
        exact hσ.comp _ ρ
      rw [hz, e, ← hL, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    · funext i b
      have e : (fun q => zOf θ V W hr X idx x w b (idx.symm q)) =
          L (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) := by
        funext q
        rw [hz, Equiv.apply_symm_apply, hL]
      rw [hp, e, LinearEquiv.symm_apply_apply]
      refine sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)
      · have e1 : finPart D (w i b) = 0 := congrFun (congrFun hw i) b
        rw [RingHom.map_sub, hσ.fin, e1, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_sub, hσ.comp, sub_eq_zero]
        show realM θ w (tauE D ρ) i b = _
        rw [realM_tauE]
        rfl

end GlobalTheory.AdTh.RealCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_idemOf_coeff_eq_self : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ) (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X → ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  first | exact @GlobalTheory.CuspMult.idemOf_coeff_real | exact GlobalTheory.CuspMult.idemOf_coeff_real | (intros; apply GlobalTheory.CuspMult.idemOf_coeff_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LatLoc

theorem loc_transfer {R : Type} [CommRing R] {n : ℕ} {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ)
    (u : S) (ε : R) (hu : (u : R) * N = ε) (hε : ε * ε = ε) (h : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (z : Fin n → R)
    (hz : (fun a => ε * z a) ∈ H₀) : (fun a => ε * z a) ∈ H₁ := by
  have h1 := H₁.smul_mem u (h _ hz)
  convert h1 using 1
  funext a
  show ε * z a = (u : R) * ((N : R) * (ε * z a))
  rw [← mul_assoc, hu, ← mul_assoc, hε]

set_option maxHeartbeats 800000 in

theorem lamHat_loc : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (PP : Pl D.host.E) (e : Formalism.L2.Theta.AE D), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → Formalism.L2.NTheta.IsIdemAt e PP → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (y ∈ Formalism.L2.NTheta.LamHat V → (fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V) ∧ ((fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, (β⁻¹).val.mulVec (fun a => swapAE D (finPart D e * y a)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  intro D V β Λ N PP e hB hN he y
  obtain ⟨hfr, -, -, h01, h10⟩ := hB
  have hee : e * e = e := he.1.1
  have key : ∀ z, z ∈ Formalism.L2.NTheta.LamHat V ↔
      (fun i => swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) :=
    fun z => GlobalTheory.LevSplit.latHat_iff (GlobalTheory.LevSplit.L0sub V) z
  have hint : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * GlobalTheory.LevSplit.finSw D (incA D (x : D.host.E)) = GlobalTheory.LevSplit.finSw D e := by
    intro x hx
    have x0 : x ≠ 0 := fun h0 => hx (h0 ▸ PP.asIdeal.zero_mem)
    have hm := GlobalTheory.LevSplit.swapAE_int (not_not.1 fun hn => hx ((he.2 x x0).2 hn))
    refine ⟨⟨_, hm⟩, ?_⟩
    show GlobalTheory.LevSplit.finSw D (e * incA D ((x : D.host.E)⁻¹)) * _ = _
    have : (x : D.host.E) ≠ 0 := by simpa using x0
    rw [← map_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ this, map_one, mul_one]
  obtain ⟨u, hu⟩ := hint N hN
  have hu' : (u : EAf D) * (N : EAf D) = GlobalTheory.LevSplit.finSw D e := by
    rw [← hu]
    congr 1
  obtain ⟨φ, hφ⟩ := hint 1 (fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
  have hφ' : (φ : EAf D) = GlobalTheory.LevSplit.finSw D e := by
    rw [← hφ]
    simp
  have hε : GlobalTheory.LevSplit.finSw D e * GlobalTheory.LevSplit.finSw D e = GlobalTheory.LevSplit.finSw D e := by
    rw [← map_mul, hee]
  have hsw : (fun a => swapAE D (finPart D e * y a)) = fun a => GlobalTheory.LevSplit.finSw D e * swapAE D (y a) :=
    funext fun a => map_mul _ _ _
  have a01 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) Λ N h01
  have a10 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) Λ (GlobalTheory.LevSplit.L0sub V) N h10
  constructor
  · intro hy
    refine (key _).2 ?_
    rw [hsw, ← hφ']
    exact Submodule.smul_mem _ φ ((key y).1 hy)
  · refine (key _).trans (Iff.trans ?_ (hfr _))
    rw [hsw]
    exact ⟨loc_transfer _ _ N u _ hu' hε a01 _, loc_transfer _ _ N u _ hu' hε a10 _⟩

end GlobalTheory.LatLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilInner

theorem integral_mul_conj_self {G : Type} [MeasurableSpace G] (ν : Measure G) {f : G → ℂ} (hf : Measurable f) :
    ∫ w, f w * conj (f w) ∂ν = ((∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal : ℂ) := by
  have e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_mul_conj {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) (bf : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (bg : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨C, hC⟩ := bf
  obtain ⟨C', hC'⟩ := bg
  refine Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem inner_eq_of_meanSquare {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (P : (G → ℂ) → Prop) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hm : ∀ f, P f → Measurable f) (hb : ∀ f, P f → ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C)
    (A : Module.End ℂ (G → ℂ)) (hA : ∀ f, P f → P (A f))
    (hu : ∀ f, P f → ∫⁻ w, ‖A f w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν) {f g : G → ℂ} (hf : P f) (hg : P g) :
    ∫ w, A f w * conj (A g w) ∂ν = ∫ w, f w * conj (g w) ∂ν := by
  have hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν := fun f g hf hg =>
    integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)
  have hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν := fun f hf => by
    rw [integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]
  have ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν =
      ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν +
        c * conj c * ∫ w, g w * conj (g w) ∂ν := by
    intro c f g hf hg
    have i1 := hI f f hf hf
    have i2 := (hI f g hf hg).const_mul (conj c)
    have i3 := (hI g f hg hf).const_mul c
    have i4 := (hI g g hg hg).const_mul (c * conj c)
    have i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν := i1.add i2
    have i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν :=
      i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2,
      ← integral_add i12 i3, ← integral_add i13 i4]
    congr 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν =
      conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν := by
    intro c
    have h := hN _ (hadd f _ hf (hsmul c g hg))
    rw [map_add, map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg] at h
    linear_combination h
  have h1 := key 1
  have h2 := key I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) *
    (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν +
      ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I

theorem om_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ p f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∫ w in 𝓕, om p f w * conj (om p f' w) ∂μ = ∫ w in 𝓕, f w * conj (f' w) ∂μ := by
  intro D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  exact inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable)
    (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p)
    (hom.om_unit μ 𝓕 hc.1 hc.2.1 p) hf hf'

end GlobalTheory.WeilInner
end

