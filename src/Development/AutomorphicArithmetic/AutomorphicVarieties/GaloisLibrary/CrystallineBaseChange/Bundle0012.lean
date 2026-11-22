import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LieX0EqRaisingLowering
section
open NumberField GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.WeightVectorLie

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (t : ℝ) : TR.Kinf F 2 :=
  ⟨!![fun _ => Real.cos t, fun _ => Real.sin t; fun _ => -Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]⟩

omit [NumberField F] in
private theorem rot_zero : rot 0 = (1 : TR.Kinf F 2) := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

private noncomputable def X0 : TR.Lie F 2 := TR.toL !![0, 1; -1, 0]

private theorem lie_X0_eq_raising_lowering [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (v : InfinitePlace F) (φ : TR.Sm F 2) :
    TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = TR.lie F 2 X0 φ := by
  unfold TR.Eop
  rw [← LinearMap.sub_apply, ← map_sub]
  congr 2
  ext i j u
  obtain rfl : u = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp [X0]

private theorem rot_deriv : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (F := F) t)).val) X0 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  fin_cases i <;> fin_cases j
  · simpa [X0, rot] using Real.hasDerivAt_cos 0
  · simpa [X0, rot] using Real.hasDerivAt_sin 0
  · simpa [X0, rot] using (Real.hasDerivAt_sin 0).fun_neg
  · simpa [X0, rot] using Real.hasDerivAt_cos 0

private theorem lie_mem [IsTotallyReal F] (U : Submodule ℂ (TR.Sm F 2)) [FiniteDimensional ℂ U]
    (hU : ∀ k, ∀ ψ ∈ U, TR.cptRep F 2 k ψ ∈ U) (ψ : TR.Sm F 2) (hψ : ψ ∈ U) : TR.lie F 2 X0 ψ ∈ U := by
  let U' : Submodule ℂ (GA F 2 → ℂ) := U.map (TR.Sm F 2).subtype
  have hcl : IsClosed (U' : Set (GA F 2 → ℂ)) := U'.closed_of_finiteDimensional
  have key : ∀ g, HasDerivAt (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) ((TR.lie F 2 X0 ψ).1 g) 0 := fun g =>
    TR.hasDerivAt_curve ψ g (fun t => Unitary.toUnits (rot t)) X0 (by rw [rot_zero, map_one]) rot_deriv
  have hm : (TR.lie F 2 X0 ψ).1 ∈ U' := by
    refine hcl.mem_of_tendsto (b := nhdsWithin (0 : ℝ) {0}ᶜ)
      (f := fun t g => slope (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) 0 t)
      (tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (key g)) (Filter.Eventually.of_forall fun t => ?_)
    exact U'.smul_of_tower_mem ((t - 0)⁻¹ : ℝ)
      (U'.sub_mem (Submodule.mem_map_of_mem (hU (rot t) ψ hψ)) (Submodule.mem_map_of_mem (hU (rot 0) ψ hψ)))
  obtain ⟨χ, hχ, e⟩ := hm
  rwa [← Subtype.ext e]

private theorem eig_abs {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (D : Module.End ℂ M)
    (hD : ∀ U : Submodule ℂ M, FiniteDimensional ℂ U → (∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U) → ∀ ψ ∈ U, D ψ ∈ U)
    (V : Submodule ℂ M) (φ : M) (hφ0 : φ ≠ 0) (hV : ∀ k, ρ k φ ∈ V)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k φ))) :
    ∃ ψ ∈ V, ψ ≠ 0 ∧ ∃ z : ℂ, D ψ = z • ψ := by
  let U : Submodule ℂ M := Submodule.span ℂ (Set.range fun k => ρ k φ)
  have hUV : U ≤ V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hV k)
  have hU : ∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U := fun k ψ hψ => by
    have h : U ≤ U.comap (ρ k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      exact Submodule.subset_span ⟨k * k', by simp⟩)
    exact h hψ
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial U := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (D.restrict (hD U hf hU))
  obtain ⟨ψ, hψ⟩ := hz.exists_hasEigenvector
  exact ⟨ψ.1, hUV ψ.2, fun h => hψ.2 (Subtype.ext h), z, congrArg Subtype.val hψ.apply_eq_smul⟩

private theorem act_cpt [IsTotallyReal F] (k : TR.Kinf F 2) : TR.act (.cpt k) = TR.cptRep F 2 k := by
  rw [TR.act]

private theorem eig [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (π : TR.CuspSub F 2) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ z : ℂ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨ψ, h1, h2, z, h3⟩ := eig_abs (TR.cptRep F 2) (TR.lie F 2 X0) (fun U _ hU => lie_mem U hU) π.V φ hφ0
    (fun k => by rw [← act_cpt]; exact π.stable _ φ hφ) (π.cusp φ hφ).1.kfin
  exact ⟨ψ, h1, h2, z, fun v => (lie_X0_eq_raising_lowering v ψ).trans h3⟩

private theorem int_of [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (ψ : TR.Sm F 2) (h0 : ψ ≠ 0) (z : ℂ)
    (he : ∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = z • ψ) : ∃ n : ℤ, z = Complex.I * n := by
  have hr : IsRot (F := F) (fun _ => 2 * Real.pi) 1 := by
    ext i j v
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨g, hg⟩ : ∃ g, ψ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  have h1 := rotEig F ψ z he _ _ hr g
  rw [map_one, mul_one] at h1
  have h2 : Complex.exp (z * (2 * Real.pi)) = 1 := by
    have h3 := mul_right_cancel₀ hg (h1.symm.trans (one_mul _).symm)
    have : Unique (InfinitePlace F) := uniqueOfSubsingleton (Classical.arbitrary _)
    simpa using h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply mul_right_cancel₀ hpi
  rw [hn]; ring

end UpperTheory.V.Br.WeightVectorLie

open UpperTheory.V.Br.WeightVectorLie in
theorem UpperTheory.V.Br.wtVec :
    UpperTheory.V.Br.WtVec := by
  intro π
  obtain ⟨φ, hφ, h0, z, he⟩ := eig π
  obtain ⟨n, rfl⟩ := int_of φ h0 z he
  exact ⟨φ, hφ, h0, n, he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low
section
namespace UpperTheory.V.Br

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ}

private theorem wt_low (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

private theorem cas (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by
    rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

private theorem bound (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    {x : V} (hx0 : x ≠ 0) {n : ℤ} (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push_neg at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs,
      h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

private theorem descend (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx0 hx
  have hb := bound hL hC h0 hW hH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j <;> (push_cast at hb; nlinarith)
  by_cases hL0 : L x = 0
  · refine ⟨x, hx0, ?_, hL0⟩
    have hc := cas hC hx
    rw [hL0, map_zero] at hc
    have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
      rcases smul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd h hx0
    have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
        linear_combination 4 * hq
      exact_mod_cast h4
    have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
    have hjk : j = k := by
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · omega
    rw [hx, hjk]
    simp
  · have hwl := wt_low hL hx
    refine ih (j - 2) (by omega) (L x) hL0 ?_
    rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

end

theorem sl2Low : UpperTheory.V.Br.Sl2Low := by
  intro V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

end UpperTheory.V.Br
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w 2) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w 2) (KGL w 2) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2 := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem UpperTheory.V.Br.uOfSat :
    UpperTheory.V.Br.UOfSat := by
  intro F _ _ w V _ _ ρ x α β ⟨_, hx', _, h⟩
  have hx := GlobalTheory.LGrp.mem_fixed.1 hx'
  constructor
  · have h1 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 1 (by norm_num)
    rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h1]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := rfl
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 2 (by norm_num)
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
end
end

