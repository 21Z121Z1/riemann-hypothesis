import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.MatVTransvection
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def matV {n : Type} [Fintype n] (Γ : Matrix n n K) : (n → V) →ₗ[K] (n → V) :=
  LinearMap.pi fun k => ∑ l, Γ k l • LinearMap.proj l

theorem matV_apply {n : Type} [Fintype n] (Γ : Matrix n n K) (x : n → V) (k : n) :
    matV Γ x k = ∑ l, Γ k l • x l := by
  simp [matV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem matV_mul {n : Type} [Fintype n] (A B : Matrix n n K) :
    (matV (A * B) : (n → V) →ₗ[K] (n → V)) = matV A ∘ₗ matV B := by
  apply LinearMap.ext; intro x; funext k
  simp only [matV_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem matV_one {n : Type} [Fintype n] [DecidableEq n] :
    (matV (1 : Matrix n n K) : (n → V) →ₗ[K] (n → V)) = LinearMap.id := by
  apply LinearMap.ext; intro x; funext k
  simp [matV_apply, Matrix.one_apply, ite_smul]

theorem matV_inv_cancel {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A (matV A⁻¹ x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem matV_inv_cancel' {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A⁻¹ (matV A x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem map_matV_pi {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (S : Submodule K V) :
    (Submodule.pi Set.univ fun _ : n => S).map (matV A) = Submodule.pi Set.univ fun _ : n => S := by
  have hsub : ∀ B : Matrix n n K, ∀ x ∈ (Submodule.pi Set.univ fun _ : n => S), matV B x ∈
      (Submodule.pi Set.univ fun _ : n => S) := by
    intro B x hx k _
    rw [matV_apply]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact hsub A x hx
  · intro x hx
    exact ⟨matV A⁻¹ x, hsub _ x hx, matV_inv_cancel A hA x⟩

def latPow (n : Type) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) (n → V) := Submodule.pi Set.univ fun _ : n => M

theorem span_latPow {n : Type} [Fintype n] [DecidableEq n] (M : Submodule (𝓞 K) V) :
    Submodule.span K ((latPow n M : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => Submodule.span K (M : Set V) :=
  span_pi_eq _

theorem span_map_matV {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0)
    (L : Submodule (𝓞 K) (n → V)) (S : Submodule K V)
    (hL : Submodule.span K (L : Set (n → V)) = Submodule.pi Set.univ fun _ : n => S) :
    Submodule.span K ((L.map ((matV A).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => S := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL, map_matV_pi A hA]

theorem matV_transvection {n : Type} [Fintype n] [DecidableEq n] (i j : n) (c : K) (x : n → V) :
    matV (Matrix.transvection i j c) x = x + Pi.single i (c • x j) := by
  funext k
  rw [matV_apply]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
    Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Pi.add_apply]
  by_cases hk : i = k
  · subst hk; simp
  · simp [hk, Pi.single_apply, Ne.symm hk]

theorem idx_matV (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {n : Type} [Fintype n] [DecidableEq n]
    (M : Submodule (𝓞 K) V) (hM : M.FG) (A : Matrix n n K) (hA : A.det ≠ 0) :
    idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det := by
  have hLfg : (latPow n M).FG := Submodule.fg_pi fun _ => hM
  have hsp := span_latPow (n := n) M
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det) A hA ?_ ?_ ?_
  ·
    intro D hD
    have hDk : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)
    have hmap : (latPow n M).map ((matV (Matrix.diagonal D)).restrictScalars (𝓞 K)) =
        Submodule.pi Set.univ fun k => smulSub (D k) M := by
      ext x
      simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mem_pi, Set.mem_univ,
        true_implies, latPow, mem_smulSub]
      constructor
      · rintro ⟨y, hy, rfl⟩ k
        exact ⟨y k, hy k, by rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul]⟩
      · intro h
        choose y hy hyx using h
        exact ⟨y, hy, by funext k; rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul, hyx]⟩
    rw [hmap, latPow, idx_pi hI w _ _ (fun _ => hM) (fun k => fg_smulSub _ M hM)
      (fun k => (span_smulSub _ (hDk k) M).symm), Matrix.det_diagonal,
      vAdd_prod w _ _ (fun k _ => hDk k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => idx_smulSub hI w (D k) (hDk k) M hM
  ·
    intro t
    rw [Matrix.TransvectionStruct.toMatrix, Matrix.det_transvection_of_ne _ _ t.hij]
    have hv1 : vAdd w (1 : K) = 0 := by simp [vAdd]
    rw [hv1, mul_zero]
    set φ : (n → V) →ₗ[K] (n → V) := LinearMap.id - (LinearMap.single K (fun _ => V) t.i) ∘ₗ LinearMap.proj t.i
      with hφ
    have hφapp : ∀ x : n → V, φ x = x - Pi.single t.i (x t.i) := fun x => by simp [hφ]
    have hφT : φ ∘ₗ matV (Matrix.transvection t.i t.j t.c) = φ := by
      apply LinearMap.ext; intro x
      rw [LinearMap.comp_apply, hφapp, hφapp, matV_transvection]
      funext k
      by_cases hk : k = t.i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    have hker0 : ∀ z : n → V, φ z = 0 ↔ ∀ k, k ≠ t.i → z k = 0 := by
      intro z
      rw [hφapp]
      constructor
      · intro h k hk
        have := congrFun h k
        simpa [Pi.single_apply, hk] using this
      · intro h
        funext k
        by_cases hk : k = t.i
        · subst hk; simp
        · simp [Pi.single_apply, hk, h k hk]
    have hfix : ∀ z : n → V, φ z = 0 → matV (Matrix.transvection t.i t.j t.c) z = z := by
      intro z hz
      rw [matV_transvection, (hker0 z).mp hz t.j (Ne.symm t.hij), smul_zero, Pi.single_zero, add_zero]
    have hT := span_map_matV (Matrix.transvection t.i t.j t.c)
      (by rw [Matrix.det_transvection_of_ne _ _ t.hij]; exact one_ne_zero) (latPow n M) _ hsp
    rw [idx_map hI w φ _ _ hLfg (hLfg.map _) (by rw [hT, hsp])]
    · rw [← Submodule.map_comp]
      have : ((φ.restrictScalars (𝓞 K)).comp ((matV (Matrix.transvection t.i t.j t.c)).restrictScalars (𝓞 K))) =
          φ.restrictScalars (𝓞 K) := by
        rw [← LinearMap.restrictScalars_comp, hφT]
      rw [this, idx_self]
    · ext z
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨hz, hz0⟩
        exact ⟨⟨z, hz, hfix z hz0⟩, hz0⟩
      · rintro ⟨⟨x, hx, rfl⟩, hz0⟩
        have hx0 : φ x = 0 := by
          rw [← hz0, ← LinearMap.comp_apply, hφT]
        rw [hfix x hx0]
        exact ⟨hx, by rw [hfix x hx0] at hz0; exact hz0⟩
  ·
    intro A B hA hB hPA hPB
    have hsB := span_map_matV B hB (latPow n M) _ hsp
    have hsA := span_map_matV A hA (latPow n M) _ hsp
    have hsAB := span_map_matV A hA _ _ hsB
    have hcomp : (latPow n M).map ((matV (A * B)).restrictScalars (𝓞 K)) =
        ((latPow n M).map ((matV B).restrictScalars (𝓞 K))).map ((matV A).restrictScalars (𝓞 K)) := by
      rw [← Submodule.map_comp, matV_mul, LinearMap.restrictScalars_comp]
    rw [hcomp, idx_chain hI w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) _ hLfg
      (hLfg.map _) ((hLfg.map _).map _) (by rw [hsA, hsp]) (by rw [hsAB, hsA])]
    have hinj : ∀ P : Submodule (𝓞 K) (n → V), ∀ x ∈ P, matV A x = 0 → x = 0 := by
      intro P x _ hx
      rw [← matV_inv_cancel' A hA x, hx, map_zero]
    rw [← idx_map_inj hI w (matV A) (latPow n M) _ hLfg (hLfg.map _) (by rw [hsB, hsp]) (hinj _) (hinj _),
      hPA, hPB, Matrix.det_mul, vAdd_mul w _ _ hA hB]
    ring

end Gen

end PI.Dv.TIW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.PerS
section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section PerS

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem perS (T : GoodSet K G) (P0 P : Pair K G) (hM1 : M1 T P0) (s : T.S) :
    ∃ (g g' : Fin (nS T P s) → G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      (∀ j k, algebraMap (𝓞 K) K (Γ j k) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))))) ∧
      Γ.det ≠ 0 ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, (epsS P * MonoidAlgebra.of K G (g i)) * b' i * (eps P * eS T s) = eps P * eS T s := by
  classical
  set τ := T.tau s with hτ
  set p := τ.asAlgebraHom (eps P) with hp_def
  set p0 := τ.asAlgebraHom (eps P0) with hp0_def
  have hp : p * p = p := tau_eps_idem τ P
  have hp0 : p0 * p0 = p0 := tau_eps_idem τ P0
  have h1 : Module.finrank K (LinearMap.range p0) = 1 := hM1 s
  set n := nS T P s with hn_def
  have hn : Module.finrank K (LinearMap.range p) = n := by rw [hn_def]; rfl
  clear_value n

  obtain ⟨v0', hv0ne, hv0⟩ := finrank_eq_one_iff'.mp h1
  set v0 : T.W s := v0'.1 with hv0_def
  have hv0ne' : v0 ≠ 0 := fun h => hv0ne (Subtype.ext h)
  have hpv0 : p0 v0 = v0 := by
    obtain ⟨w, hw⟩ := v0'.2
    rw [hv0_def, ← hw, ← Module.End.mul_apply, hp0]
  obtain ⟨f0, hf0⟩ := exists_dual_one (K := K) v0 hv0ne'
  have hline : ∀ w, p0 w = f0 (p0 w) • v0 := by
    intro w
    obtain ⟨c, hc⟩ := hv0 ⟨p0 w, LinearMap.mem_range_self _ _⟩
    have hc' : c • v0 = p0 w := congrArg Subtype.val hc
    rw [← hc', map_smul, hf0, smul_eq_mul, mul_one]

  let pc : T.W s →ₗ[K] LinearMap.range p := LinearMap.codRestrict _ p (fun w => LinearMap.mem_range_self p w)
  let F : G → LinearMap.range p := fun x => pc (τ x v0)
  have hF : Submodule.span K (Set.range F) = ⊤ := by
    have : Set.range F = pc '' Set.range (fun x => τ x v0) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, span_orbit τ (T.irr s) v0 hv0ne', Submodule.map_top, LinearMap.range_eq_top]
    rintro ⟨u, w, rfl⟩
    exact ⟨w, rfl⟩
  obtain ⟨g0, hg0⟩ := select_li F hF
  let g : Fin n → G := g0 ∘ Fin.cast hn.symm
  have hg : LinearIndependent K (F ∘ g) := hg0.comp _ (Fin.cast_injective _)

  let ψ : G → Module.Dual K (LinearMap.range p) := fun x =>
    (f0 ∘ₗ p0 ∘ₗ τ x) ∘ₗ (LinearMap.range p).subtype
  have hψapp : ∀ x (u : LinearMap.range p), ψ x u = f0 (p0 (τ x u)) := fun x u => rfl
  have hψ : ∀ u : LinearMap.range p, (∀ x, ψ x u = 0) → u = 0 := by
    intro u hu
    by_contra hne
    have hne' : (u : T.W s) ≠ 0 := fun h => hne (Subtype.ext h)
    have hall : ∀ w, f0 (p0 w) = 0 := by
      intro w
      have hw : w ∈ Submodule.span K (Set.range fun x => τ x u) := by
        rw [span_orbit τ (T.irr s) u hne']; trivial
      induction hw using Submodule.span_induction with
      | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hu x
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]
    have := hall v0
    rw [hpv0, hf0] at this
    exact one_ne_zero this
  have hψspan := dual_span ψ hψ
  obtain ⟨g'0, hg'0⟩ := select_li ψ hψspan
  have hdn : Module.finrank K (Module.Dual K (LinearMap.range p)) = n := by
    rw [Subspace.dual_finrank_eq, hn]
  let g' : Fin n → G := g'0 ∘ Fin.cast hdn.symm
  have hg' : LinearIndependent K (ψ ∘ g') := hg'0.comp _ (Fin.cast_injective _)
  have hg'span : Submodule.span K (Set.range (ψ ∘ g')) = ⊤ := li_span_top _ hg' hdn.symm
  have hgspan : Submodule.span K (Set.range (F ∘ g)) = ⊤ := li_span_top _ hg hn.symm

  set cH : K := ((Nat.card P.H : ℕ) : K) with hcH
  set cH0 : K := ((Nat.card P0.H : ℕ) : K) with hcH0
  have hcH_ne : cH ≠ 0 := by rw [hcH]; exact_mod_cast (card_H_pos P).ne'
  have hcH0_ne : cH0 ≠ 0 := by rw [hcH0]; exact_mod_cast (card_H_pos P0).ne'
  have hτepsS : τ.asAlgebraHom (epsS P) = cH • p := by rw [epsS_eq_smul, map_smul]
  have hτepsS0 : τ.asAlgebraHom (epsS P0) = cH0 • p0 := by rw [epsS_eq_smul, map_smul]
  have hmem : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) ∈
        Set.range (algebraMap (𝓞 K) K) := fun j k =>
    trace_mem_of_intR τ _ (intR_mul (intR_mul (intR_epsS P0) (intR_of _)) (intR_mul (intR_epsS P) (intR_of _)))
  choose Γf hΓf using hmem
  let Γ : Matrix (Fin n) (Fin n) (𝓞 K) := Matrix.of Γf
  have hkey : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) =
        cH0 * cH * ψ (g' j) (F (g k)) := by
    intro j k
    set X := τ (g' j) * p * τ (g k) with hX
    have e1 : τ.asAlgebraHom (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))) =
        (cH0 * cH) • (p0 * X) := by
      rw [map_mul, map_mul, map_mul, hτepsS, hτepsS0, Representation.asAlgebraHom_of,
        Representation.asAlgebraHom_of, hX]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      rw [mul_comm cH cH0]
    have e2 : LinearMap.trace K (T.W s) (p0 * X) = f0 (p0 (X v0)) := by
      have hs := rank_one_sandwich p0 hp0 h1 X
      have := congrArg (fun M : Module.End K (T.W s) => f0 (M v0)) hs
      simp only [Module.End.mul_apply, LinearMap.smul_apply, hpv0, map_smul, hf0, smul_eq_mul, mul_one] at this
      exact this.symm
    rw [e1, map_smul, e2, smul_eq_mul, hψapp]
    rfl
  let A : Matrix (Fin n) (Fin n) K := Matrix.of fun j k => ψ (g' j) (F (g k))
  have hΓK : Γ.map (algebraMap (𝓞 K) K) = (cH0 * cH) • A := by
    ext j k
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, A]
    show algebraMap (𝓞 K) K (Γf j k) = _
    exact (hΓf j k).trans (hkey j k)
  have hAdet : A.det ≠ 0 := by
    intro hA
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
    set w : LinearMap.range p := ∑ k, c k • F (g k) with hw
    have hψw : ∀ j, ψ (g' j) w = 0 := by
      intro j
      have := congrFun hc j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, A, Pi.zero_apply] at this
      rw [hw, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hall : ∀ φ : Module.Dual K (LinearMap.range p), φ w = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span K (Set.range (ψ ∘ g')) := by rw [hg'span]; trivial
      induction hφ using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hψw j
      | zero => rfl
      | add y z _ _ hy hz => rw [LinearMap.add_apply, hy, hz, add_zero]
      | smul a y _ hy => rw [LinearMap.smul_apply, hy, smul_zero]
    have hw0 : w = 0 := (Module.forall_dual_apply_eq_zero_iff K w).mp hall
    have := Fintype.linearIndependent_iff.mp hg c (by rw [← hw0, hw]; rfl)
    exact hc0 (funext this)
  have hdetK : (Γ.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [hΓK, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hcH0_ne hcH_ne)) hAdet
  have hdetΓ : Γ.det ≠ 0 := by
    intro h
    apply hdetK
    rw [show Γ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K).mapMatrix Γ from rfl, ← RingHom.map_det, h,
      map_zero]
  refine ⟨g, g', Γ, fun j k => hΓf j k, hdetΓ, ?_⟩

  set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓKd
  set δ := ΓK.det with hδ
  let b : Fin n → MonoidAlgebra K G := fun j => epsS P0 * MonoidAlgebra.of K G (g' j)
  let a : Fin n → MonoidAlgebra K G := fun k => epsS P * MonoidAlgebra.of K G (g k)
  let b' : Fin n → MonoidAlgebra K G := fun i => δ⁻¹ • ∑ j, ΓK.adjugate i j • b j
  have hbY : ∀ j, b j * (eps P * eS T s) = eps P0 * eS T s * b j * (eps P * eS T s) := by
    intro j
    have := absorb_eps T s P0 P (MonoidAlgebra.of K G (g' j))
    exact this.symm
  refine ⟨b', fun i => ?_, ?_⟩
  · simp only [b', smul_mul_assoc, Finset.sum_mul, mul_smul_comm, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbY j]
  ·
    have hδ0 : δ ≠ 0 := hdetK
    have hbu : ∀ j k, τ.asAlgebraHom (b j) (F (g k) : T.W s) = (ΓK j k * cH⁻¹) • v0 := by
      intro j k
      have hΓ : ΓK j k = cH0 * cH * ψ (g' j) (F (g k)) := (hΓf j k).trans (hkey j k)
      have hb : τ.asAlgebraHom (b j) = cH0 • (p0 * τ (g' j)) := by
        simp only [b, map_mul, hτepsS0, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [hb, LinearMap.smul_apply, Module.End.mul_apply, hline (τ (g' j) _), smul_smul, hΓ]
      congr 1
      rw [hψapp]
      field_simp
    have hb'u : ∀ i k, τ.asAlgebraHom (b' i) (F (g k) : T.W s) =
        (cH⁻¹ * (1 : Matrix (Fin n) (Fin n) K) i k) • v0 := by
      intro i k
      simp only [b', map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, hbu, smul_smul,
        ← Finset.sum_smul]
      congr 1
      have hadj : ∑ j, ΓK.adjugate i j * ΓK j k = δ * (1 : Matrix (Fin n) (Fin n) K) i k := by
        have := congrFun (congrFun (Matrix.adjugate_mul ΓK) i) k
        rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
        exact this
      have : ∑ j, ΓK.adjugate i j * (ΓK j k * cH⁻¹) = (∑ j, ΓK.adjugate i j * ΓK j k) * cH⁻¹ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hadj]
      field_simp
    set Z' : Module.End K (T.W s) := ∑ i, τ.asAlgebraHom (a i) * τ.asAlgebraHom (b' i) with hZ'
    have hZk : ∀ k, Z' (F (g k) : T.W s) = (F (g k) : T.W s) := by
      intro k
      rw [hZ', LinearMap.sum_apply]
      simp only [Module.End.mul_apply, hb'u, map_smul]
      rw [Finset.sum_eq_single k (fun x _ hx => by rw [Matrix.one_apply_ne hx, mul_zero, zero_smul])
        (by simp), Matrix.one_apply_eq, mul_one]
      have ha : τ.asAlgebraHom (a k) = cH • (p * τ (g k)) := by
        simp only [a, map_mul, hτepsS, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [ha, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hcH_ne, one_smul, Module.End.mul_apply]
      rfl
    have hrange : ∀ u ∈ LinearMap.range p, u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)) := by
      intro u hu
      have h2 : (⟨u, hu⟩ : LinearMap.range p) ∈ Submodule.span K (Set.range (F ∘ g)) := by
        rw [hgspan]; trivial
      have h3 := Submodule.mem_map_of_mem (f := (LinearMap.range p).subtype) h2
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact h3
    have hZsp : ∀ u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)), Z' u = u := by
      intro u hsp
      induction hsp using Submodule.span_induction with
      | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hZk k
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy]
    have hZu : ∀ u ∈ LinearMap.range p, Z' u = u := fun u hu => hZsp u (hrange u hu)
    have hZ : τ.asAlgebraHom (∑ i, a i * b' i * eps P) = p := by
      rw [map_sum]
      simp only [map_mul]
      rw [← Finset.sum_mul, ← hZ']
      apply LinearMap.ext; intro w
      rw [Module.End.mul_apply, hZu _ (LinearMap.mem_range_self p w)]
    calc ∑ i, a i * b' i * (eps P * eS T s) = (∑ i, a i * b' i * eps P) * eS T s := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
      _ = eps P * eS T s := mul_eS_eq T s _ _ (by rw [hZ])

end PerS

end PI.Dv.TIW
end
end

