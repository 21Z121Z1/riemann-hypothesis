import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHolomorphicLowestKTypeComplexified
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.LowTau

theorem exp_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have hc : ∀ B : Matrix (Fin n) (Fin n) ℂ, B.map star = Bᴴᵀ := fun B => by ext i j; simp
  rw [hc, hc, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose]

theorem inG_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) :
    inG ε (X.map star) := by
  unfold inG at h ⊢
  have hJ : (Jm ε)ᵀ = Jm ε := by unfold Jm; simp
  have e1 : (X.map star)ᴴ = Xᵀ := by ext i j; simp
  have e2 : Xᴴᵀ = X.map star := by ext i j; simp
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hJ, e2, Matrix.transpose_zero] at h2
  rw [e1, add_comm]
  exact h2

theorem exists_tau : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  intro n ε Λ H V _ _ _ _ σ E ι u hσ hD hu hK hW
  set S : Submodule ℂ H := (Formalism.REAL.kSpan ε E u).map ι.toLinearMap with hS
  have huk : u ∈ Formalism.REAL.kSpan ε E u := by
    unfold Formalism.REAL.kSpan
    exact Submodule.mem_sInf.2 fun _ h => h.1
  have huS : ι u ∈ S := Submodule.mem_map_of_mem huk
  have hKU : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    obtain ⟨hgu, hgc⟩ := hg
    have h1 : gᴴ * g = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hgu
    show gᴴ * Jm ε * g = Jm ε
    rw [Matrix.mul_assoc, ← hgc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hexpK : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → NormedSpace.exp Z ∈ Formalism.REAL.Kset ε := by
    intro Z hZ
    obtain ⟨hg, hc⟩ := hZ
    unfold inG at hg
    have hZH : Zᴴ = -Z := by
      have h1 : Zᴴ * Jm ε = -(Z * Jm ε) := by
        rw [hc]; exact eq_neg_of_add_eq_zero_left hg
      calc Zᴴ = Zᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
        _ = -Z := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    refine ⟨?_, (Commute.exp_left (show Commute Z (Jm ε) from hc)).eq⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hZH,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have hσK : IsURepOn (Formalism.REAL.Kset ε) σ := by
    obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
    exact ⟨⟨h1, fun a ha b hb => hm a (hKU ha) b (hKU hb)⟩, fun g hg => hn g (hKU hg),
      fun v => (hc v).mono hKU⟩
  have hwS : ‖(⟨ι u, huS⟩ : S)‖ = 1 := by
    show ‖(ι u : H)‖ = 1
    simp [hu]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε Λ H σ S ⟨ι u, huS⟩ hσK hK hwS hW
  let e := Submodule.equivMapOfInjective ι.toLinearMap ι.injective (Formalism.REAL.kSpan ε E u)
  have heι : ∀ x : S, ι (e.symm x : V) = (x : H) := by
    intro x
    have h0 : ((e (e.symm x) : S) : H) = ι (e.symm x : V) := rfl
    rw [LinearEquiv.apply_symm_apply] at h0
    exact h0.symm
  let j : S →ₗᵢ[ℂ] V :=
    { toLinearMap := (Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap
      norm_map' := fun x => by
        show ‖(e.symm x : V)‖ = ‖x‖
        rw [← ι.norm_map, heι, Submodule.coe_norm] }
  have hjι : ∀ x : S, ι (j x) = (x : H) := heι
  refine ⟨S, inferInstance, inferInstance, τ, ⟨ι u, huS⟩, j, hτ, ι.injective (hjι _), ?_, ?_⟩
  · show LinearMap.range ((Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap) = _
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · intro Y hY v v' hv'
    have hX : inG ε (Y.map star) := inG_conj hY.1
    have hsm : ∀ t : ℝ, inK ε ((t : ℂ) • Y) := by
      intro t
      obtain ⟨hg, hc⟩ := hY
      unfold inG at hg
      refine ⟨?_, ?_⟩
      · unfold inG
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
          Matrix.mul_smul, ← smul_add, hg, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
    have hpt : ∀ t : ℝ, ((τ (NormedSpace.exp ((t : ℂ) • Y)) v : S) : H) =
        σ (NormedSpace.exp ((t : ℂ) • Y.map star)) v := by
      intro t
      rw [hτσ _ (hexpK _ (hsm t)), exp_conj]
      congr 3
      ext a b
      simp
    have hd := hD (Y.map star) hX (j v)
    rw [hjι, ← hv', hjι] at hd
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    refine Asymptotics.isLittleO_norm_left.mp ?_
    refine (Asymptotics.isLittleO_norm_left.mpr hd).congr_left fun t => ?_
    rw [Submodule.coe_norm]
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, hpt]

end GlobalTheory.SphJet.LowTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsEqZeroOfNil
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

section

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ}
  {u : V} {j : W →ₗᵢ[ℂ] V}

theorem LowData.mem_kSpan (hL : LowData ε E Λ u j) (x : W) : j x ∈ Formalism.REAL.kSpan ε E u := by
  rw [← hL.2.2.2.2]; exact ⟨x, rfl⟩

theorem LowData.exists_of_mem (hL : LowData ε E Λ u j) {v : V} (hv : v ∈ Formalism.REAL.kSpan ε E u) :
    ∃ x : W, j x = v := by
  rw [← hL.2.2.2.2] at hv
  exact hv

theorem LowData.finiteDimensional (hL : LowData ε E Λ u j) : FiniteDimensional ℂ W := by
  have h := hL.2.2.2.1
  rw [← hL.2.2.2.2] at h
  exact (LinearEquiv.ofInjective j.toLinearMap j.injective).symm.finiteDimensional

theorem LowData.exists_arr (hL : LowData ε E Λ u j) {k : ℕ} {F : Arr V n k} (hF : F ∈ arrV0 ε E u k) :
    ∃ G : (Fin k → Fin n × Fin n) → W, arrTo V n k (fun α => j (G α)) = F := by
  have h : ∀ α, ∃ x : W, j x = F α := by
    intro α
    have h1 := (mem_admissibleArrays ε E u F).mp hF α
    apply hL.exists_of_mem
    split_ifs at h1
    · exact h1
    · rw [(Submodule.mem_bot ℂ).mp h1]; exact Submodule.zero_mem _
  choose G hG using h
  exact ⟨G, indexArray_ext fun α => hG α⟩

theorem arrTo_apply_jet {k : ℕ} (f : (Fin k → Fin n × Fin n) → V) (α : Fin k → Fin n × Fin n) :
    arrTo V n k f α = f α := rfl

theorem riesz_arr_mem_Nset {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hL : LowData ε E Λ u j)
    (hB : JetRel ε E Λ u j B) (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) (y : W)
    (g : (Fin (m + 1) → Fin n × Fin n) → W)
    (hg : ∀ α x, ⟪g α, x⟫_ℂ = B (List.ofFn α).reverse y x) :
    arrTo V n (m + 1) (fun α => j (g α)) ∈ Nset ε E Λ u m := by
  obtain ⟨hperm, hcomp⟩ := jetRel_perm_and_compact_vanish V W n ε E Λ u j B m hL hB h0
  have hz : ∀ α : Fin (m + 1) → Fin n × Fin n, (∃ i, ε (α i).1 = ε (α i).2) → g α = 0 := by
    rintro α ⟨i, hi⟩
    apply ext_inner_right ℂ
    intro x
    rw [hg, hcomp _ (by simp) ⟨α i, by rw [List.mem_reverse, List.mem_ofFn]; exact ⟨i, rfl⟩, hi⟩]
    simp
  have hV0 : arrTo V n (m + 1) (fun α => j (g α)) ∈ arrV0 ε E u (m + 1) := by
    rw [mem_admissibleArrays]
    intro α
    rw [arrTo_apply_jet]
    split_ifs with h
    · exact hL.mem_kSpan _
    · push Not at h
      rw [hz α h]; simp
  refine ⟨⟨hV0, ?_⟩, ?_⟩
  · simp only [symSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    intro σ
    apply indexArray_ext
    intro α
    rw [permutePositions_apply, arrTo_apply_jet, arrTo_apply_jet]
    congr 1
    apply ext_inner_right ℂ
    intro x
    rw [hg, hg, hperm _ (List.ofFn α).reverse _ (by simp)]
    exact (List.reverse_perm _).trans ((Equiv.Perm.ofFn_comp_perm σ α).trans (List.reverse_perm _).symm)
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
    intro α'
    obtain ⟨horth, hsup⟩ := typesSplit V n ε E Λ u hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1
    set S := sliceLin V n α' (arrTo V n (m + 1) (fun α => j (g α))) with hS
    have hSa : ∀ β, S β = j (g (Fin.cons (β 0) α')) := fun β => by
      rw [hS, firstPositionSlice_apply, arrTo_apply_jet]
    have hS0 : S ∈ arrV0 ε E u 1 := by
      rw [mem_admissibleArrays]
      intro β
      rw [hSa]
      split_ifs with h
      · exact hL.mem_kSpan _
      · push Not at h
        obtain ⟨i, hi⟩ := h
        rw [hz _ ⟨0, by simpa [Subsingleton.elim i 0] using hi⟩]; simp
    have hSo : ∀ Q ∈ Vminus ε E Λ u, ⟪S, Q⟫_ℂ = 0 := by
      intro Q hQ
      have hQ0 : Q ∈ arrV0 ε E u 1 := by rw [← hsup]; exact Submodule.mem_sup_right hQ
      obtain ⟨G, hG⟩ := hL.exists_arr hQ0
      have hQe : arr1 j (fun p => G fun _ => p) = Q := by
        rw [← hG]
        apply indexArray_ext
        intro β
        have : (fun _ : Fin 1 => β 0) = β := funext fun i => by rw [Subsingleton.elim i 0]
        simp only [arr1, arrTo_apply_jet, this]
      have h4 := hB.2.2.2 (List.ofFn α').reverse (fun p => G fun _ => p) (hQe ▸ hQ) y
      rw [← h4, indexArray_inner, ← hQe]
      refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun β => ?_
      rw [hSa, arr1, arrTo_apply_jet, LinearIsometry.inner_map_map, hg]
      simp [List.ofFn_succ]
    rw [← hsup] at hS0
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Submodule.mem_sup.mp hS0
    have h1 := hSo Q hQ
    rw [← hPQ, inner_add_left, horth P hP Q hQ, zero_add, inner_self_eq_zero] at h1
    rw [← hPQ, h1, add_zero]
    exact hP

theorem riesz_arr_casimir {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hL : LowData ε E Λ u j)
    (hB : JetRel ε E Λ u j B) (y : W) (g : (Fin (m + 1) → Fin n × Fin n) → W)
    (hg : ∀ α x, ⟪g α, x⟫_ℂ = B (List.ofFn α).reverse y x) (F : Arr V n (m + 1))
    (hF : arrTo V n (m + 1) (fun α => j (g α)) = F) (hN : F ∈ Nset ε E Λ u m) :
    ⟪F, CasK ε (arrE E (m + 1)) F⟫_ℂ = ((ckv ε Λ : ℝ) : ℂ) * ⟪F, F⟫_ℂ := by
  have hpair : ∀ G : (Fin (m + 1) → Fin n × Fin n) → W,
      ⟪F, arrTo V n (m + 1) (fun α => j (G α))⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (G α) := by
    intro G
    rw [indexArray_inner, ← hF]
    simp only [arrTo_apply_jet, LinearIsometry.inner_map_map, hg]
  have hst := compact_span_compact_stable ε E u
  have hy : ∀ c d : Fin n, ∃ z : W, j z = (if ε c = ε d then E c d (E d c (j y)) else 0) ∧
      ⟪F, if ε c = ε d then arrE E (m + 1) c d (arrE E (m + 1) d c F) else 0⟫_ℂ =
        ∑ α, B (List.ofFn α).reverse z (g α) := by
    intro c d
    split_ifs with h
    · have h1 := nStable V n ε E Λ u m d c h.symm F hN
      have h2 := nStable V n ε E Λ u m c d h _ h1
      obtain ⟨G₁, hG₁⟩ := hL.exists_arr h1.1.1
      obtain ⟨G₂, hG₂⟩ := hL.exists_arr h2.1.1
      obtain ⟨y₁, hy₁⟩ := hL.exists_of_mem (hst d c h.symm _ (hL.mem_kSpan y))
      obtain ⟨y₂, hy₂⟩ := hL.exists_of_mem (hst c d h _ (hL.mem_kSpan y₁))
      refine ⟨y₂, by rw [hy₂, hy₁], ?_⟩
      rw [← hG₂, hpair,
        GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB c d h y y₁ hy₁ G₁ G₂ (by rw [hG₂, hG₁]),
        GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB d c h.symm y₁ y₂ hy₂ g G₁ (by rw [hG₁, hF])]
    · exact ⟨0, by simp, by simp⟩
  choose z hz hz' using hy
  have hsum : ∑ c, ∑ d, z c d = ((ckv ε Λ : ℝ) : ℂ) • y := by
    apply j.injective
    rw [map_smul, ← kCasSpan V n ε E Λ u (glRel_kRel ε E hL.1) hL.2.2.1 _ (hL.mem_kSpan y), compactCasimir_apply]
    simp only [map_sum, hz]
  have hFF : ⟪F, F⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (g α) := by
    rw [← hpair, hF]
  rw [compactCasimir_apply, hFF]
  simp only [inner_sum, hz']
  rw [Finset.mul_sum]
  have hα : ∀ α : Fin (m + 1) → Fin n × Fin n,
      ((ckv ε Λ : ℝ) : ℂ) * B (List.ofFn α).reverse y (g α) =
        ∑ c, ∑ d, B (List.ofFn α).reverse (z c d) (g α) := by
    intro α
    have := congrArg (fun w => B (List.ofFn α).reverse w (g α)) hsum
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_ofReal] at this
    exact this.symm
  simp only [hα]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (m + 1) → Fin n × Fin n))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

end

theorem jetRel_eq_zero_of_nil :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), LowData ε E (LamOf ε lam) u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → 2 * (n : ℝ) + 1 ≤ lam a - lam b) → JetRel ε E (LamOf ε lam) u j B → B [] = 0 → ∀ l, B l = 0 := by
  intro V W _ _ _ _ n ε E lam u j B hL hgap hB hnil
  haveI := hL.finiteDimensional
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have key : ∀ m : ℕ, ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0 := by
    intro m
    induction m with
    | zero =>
      intro l hl
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
      exact hnil
    | succ m ih =>
      intro l hl
      rcases Nat.lt_or_ge m l.length with hlt | hle
      swap
      · exact ih l hle
      have hlen : l.reverse.length = m + 1 := by rw [List.length_reverse]; omega
      ext y x
      have hex : ∀ α : Fin (m + 1) → Fin n × Fin n, ∃ w : W, ∀ x, ⟪w, x⟫_ℂ = B (List.ofFn α).reverse y x :=
        fun α => ⟨(InnerProductSpace.toDual ℂ W).symm
          (LinearMap.toContinuousLinearMap (B (List.ofFn α).reverse y)), fun x => by
            rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
      choose g hg using hex
      have hN := riesz_arr_mem_Nset hL hB ih y g hg
      have hc := riesz_arr_casimir hL hB y g hg _ rfl hN
      have hp := nPos V n ε E lam (2 * (n : ℝ) + 1) u m hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hgap _ hN
      set F := arrTo V n (m + 1) (fun α => j (g α)) with hF
      rw [hc, inner_self_eq_norm_sq_to_K] at hp
      have hre : (((ckv ε (LamOf ε lam) : ℝ) : ℂ) * ((‖F‖ : ℝ) : ℂ) ^ 2).re = ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hp' : (ckv ε (LamOf ε lam) + 2 * ((m : ℝ) + 1) * (2 * (n : ℝ) + 1 - 2 * (n : ℝ))) * ‖F‖ ^ 2 ≤
          ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := hp.trans_eq hre
      have hF0 : F = 0 := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : ‖F‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖F‖, mul_nonneg hm (sq_nonneg ‖F‖)]
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
      obtain ⟨α, hα⟩ : ∃ α : Fin (m + 1) → Fin n × Fin n, List.ofFn α = l.reverse := by
        generalize l.reverse = l' at hlen
        generalize m + 1 = k at hlen
        subst hlen
        exact ⟨l'.get, List.ofFn_get l'⟩
      have hgα : g α = 0 := by
        apply j.injective
        have : F α = j (g α) := rfl
        rw [← this, hF0, map_zero]; rfl
      have := hg α x
      rw [hgα, hα, List.reverse_reverse, inner_zero_left] at this
      rw [← this]; rfl
  exact fun l => key l.length l le_rfl

end GlobalTheory.SphJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalytic
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

private lemma posDef_inv_toMK_mul_mul_toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : ((toMK k)⁻¹ * x * toMK k).PosDef := by
  have hK : toMK k ∈ Kset ε := (mem_KG ε _).1 k.2
  have hU : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hK.1
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  rw [hinv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro v₁ v₂ hv
  have := congrArg (fun v => (toMK k)ᴴ *ᵥ v) hv
  simpa [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU] using this

private lemma norm_inner_ps_exp_le_decHS_mul {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    {w : W} (hlam : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) {h : ℝ}
    (hgap : GapAtLeast ε lam h) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (u y : W) :
    ‖⟪y, ps ε lam τ w (NormedSpace.exp X) u⟫_ℂ‖ ≤
      decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖y‖ := by
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  have hint : ∀ v : W, Integrable (fun k : KG ε => ‖⟪v, τ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro v
    by_contra hn
    have hs := GlobalTheory.PsiBound.schur_norm hτ v
    rw [integral_undef hn, mul_zero] at hs
    have hv : v = 0 := by
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.1 this
    subst hv
    simp at hn
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
  rw [GlobalTheory.PsiBound.ps_entry hτ lam hP u y]
  refine GlobalTheory.PsiBound.weighted_bound (muK ε) (Module.finrank ℂ W) _ _ _ _ _ _ hM (norm_nonneg u)
    (norm_nonneg y) (fun k => GlobalTheory.PsiBound.norm_Phi_le hlam hgap hX ((mem_KG ε _).1 k.2))
    (hint y) ?_ (GlobalTheory.PsiBound.schur_norm hτ y) ?_
  · simpa only [norm_inner_symm] using hint u
  · simpa only [norm_inner_symm] using GlobalTheory.PsiBound.schur_norm hτ u

theorem ps_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  intro n ε lam W _ _ τ w hlam hτ h hgap X hX
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    rw [GlobalTheory.PsiBound.ps_entry hτ lam hP x x]
    set F : KG ε → ℂ := fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) *
      (⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) with hFdef
    have hF : ∀ k, 0 ≤ F k := by
      intro k
      have hphi : 0 < Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) :=
        (phiPos n lam _ (posDef_inv_toMK_mul_mul_toMK k hP)).2.1
      have hsq : 0 ≤ ⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ := by
        rw [← inner_conj_symm x (τ (toMK k) w), mul_comm, Complex.mul_conj]
        exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)
      exact mul_nonneg hphi.le hsq
    have hre : ∀ k, F k = ((F k).re : ℂ) := fun k =>
      Complex.ext rfl (by simpa using ((Complex.le_def.1 (hF k)).2).symm)
    have hI : ∫ k, F k ∂(muK ε) = ((∫ k, (F k).re ∂(muK ε) : ℝ) : ℂ) := by
      rw [integral_congr_ae (Eventually.of_forall hre)]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [hI]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.2 (integral_nonneg fun k => ?_))
    exact (Complex.le_def.1 (hF k)).1
  ·
    have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
    set T := ps ε lam τ w (NormedSpace.exp X)
    rcases eq_or_ne (T u) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hb := norm_inner_ps_exp_le_decHS_mul hlam hτ hgap hX u (T u)
    rw [inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hb
    have hpos : 0 < ‖T u‖ := norm_pos_iff.2 h0
    nlinarith
  ·
    obtain ⟨hopen, hpos, hdiff, -⟩ := psBasic n ε lam W τ w hlam hτ
    haveI : FiniteDimensional ℂ W := hτ.1
    haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
    let e : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
    have hg : AnalyticAt ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z))
        (e.symm (NormedSpace.exp X)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hdiff
        (hopen.mem_nhds (show Matrix.of _ ∈ U1 ε from hpos _ hP))
    have he : AnalyticAt ℂ (⇑e.symm) (NormedSpace.exp X) :=
      e.symm.toContinuousLinearMap.analyticAt _
    exact hg.comp he

end GlobalTheory.SphJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeRootArrayHighestVectorCoeffEqZeroStatement
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  first | exact @GlobalTheory.SphJet.vminus_coef | exact GlobalTheory.SphJet.vminus_coef | (intros; apply GlobalTheory.SphJet.vminus_coef <;> assumption)
end

