import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct
open UpperTheory.V.Z.Kato.Joint

namespace UpperTheory.V.Z.Kato.Joint.ThetaOperator

variable {l : ℕ} [Fact l.Prime]

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  unfold Cg at *
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h1 : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cg_lin {n : ℕ} {x y : Qbar l} (a c : Qbar l) (hc : ‖c‖ ≤ 1) (h1 : Cg n x y) :
    Cg n (a + c * x) (a + c * y) := by
  unfold Cg at *
  have e : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans h1

private theorem cg_j {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x ∈ A, ‖j x‖ ≤ 1)
    {n : ℕ} {x y : Ω} (h : CgA A l n x y) : Cg n (j x) (j y) := by
  obtain ⟨z, hz, e⟩ := h
  unfold Cg
  rw [← map_sub, e, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hj z hz)

private theorem norm_appr_sub_le_norm_pow (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)‖ ≤ ‖((l : Qbar l)) ^ n‖ := by
  have e : ((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)
      = algebraMap ℚ_[l] (PadicAlgCl l) (((-(c - ((c.appr n : ℕ) : ℤ_[l])) : ℤ_[l]) : ℚ_[l])) := by
    simp
  have e2 : ((l : Qbar l)) ^ n = algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l])) ^ n) := by simp
  rw [e, e2, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends, PadicInt.padic_norm_e_of_padicInt, norm_neg]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n c)
  refine h.trans (le_of_eq ?_)
  rw [Padic.norm_p_pow]

private theorem cg_appr (n : ℕ) (c : ℤ_[l]) (x : Qbar l) (hx : ‖x‖ ≤ 1) :
    Cg n (((c.appr n : ℕ) : Qbar l) * x) (((c : ℤ_[l]) : Qbar l) * x) := by
  unfold Cg
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_appr_sub_le_norm_pow n c) (norm_nonneg _)).trans
    (by rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx)

private theorem appr_zero' (n : ℕ) : (0 : ℤ_[l]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [PadicInt.appr]; simp [ih]

private theorem diam_cg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (hS : Std A N w j) (n a : ℕ) (b : X.Fn l)
    (ha : a.Coprime N) (hb : InChi X N w χ b) (r : ℚ) :
    Cg n (j ((thN X A N l n 1 (X.diam N l a b)).coeff r))
      (((χ a : ℤ_[l]) : Qbar l) * j ((thN X A N l n 1 b).coeff r)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS
  obtain ⟨hbB, hdiam⟩ := hb
  have hB1 : X.diam N l 1 b ∈ X.B N l w := by
    rw [hdiam 1 (Nat.coprime_one_left N)]
    exact Submodule.smul_mem _ _ hbB
  have hBa : X.diam N l a b ∈ X.B N l w := by
    rw [hdiam a ha]
    exact Submodule.smul_mem _ _ hbB
  have hψ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) b hbB).1
  have hθ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) (X.diam N l a b) hBa).1
  have hD : ∀ s : ℚ, (thN X A N l n 1 b).coeff s ∈ A := by
    obtain ⟨f, -, -, -, hd⟩ := hψ
    exact hd.1
  have hlin := GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w (X.diam N l 1 b) (X.diam N l 1 b) hB1 hB1 (χ a) 0
    (thN X A N l n 1 b) (thN X A N l n 1 b) hψ hψ
  have e : X.act l (sgD N l 1) (X.diam N l a b) = χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b := by
    rw [zero_smul, add_zero, hdiam a ha, map_smul]
    rfl
  rw [e] at hθ
  have hmem : χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b ∈ X.B N l w :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB1) (Submodule.smul_mem _ _ hB1)
  have hu := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w hw _ hmem _ _ hθ hlin r
  have h1 := cg_j hj hu
  rw [appr_zero'] at h1
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Nat.cast_zero, zero_smul, add_zero,
    smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast] at h1
  exact cg_trans h1 (cg_appr n (χ a) _ (hj _ (hD r)))

end UpperTheory.V.Z.Kato.Joint.ThetaOperator

private theorem norm_natCast_pow_le_one {l : ℕ} [Fact l.Prime] (q k : ℕ) : ‖((q : Qbar l)) ^ k‖ ≤ 1 := by
  have e : ((q : Qbar l)) ^ k = algebraMap ℚ_[l] (PadicAlgCl l) (((q : ℤ) : ℚ_[l]) ^ k) := by simp
  rw [e, PadicAlgCl.norm_extends, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one _)

private theorem coeff_div_prime_eq_zero_of_not_dvd_of_isLat {Ω : Type} [Field Ω] (φ : HahnSeries ℚ Ω) (hL : IsLat 1 φ) {q i : ℕ}
    (hq : q.Prime) (hnd : ¬ q ∣ i) : φ.coeff ((i : ℚ) / q) = 0 := by
  by_contra h
  have hden := hL _ h
  rw [Nat.cast_one, one_mul] at hden
  have key : (((i : ℚ) / q).num : ℚ) = (i : ℚ) / q := Rat.coe_int_num_of_den_eq_one hden
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h2 : (i : ℚ) = q * ((i : ℚ) / q).num := by rw [key]; field_simp
  have h3 : (i : ℤ) = q * ((i : ℚ) / q).num := by exact_mod_cast h2
  exact hnd (Int.natCast_dvd_natCast.mp ⟨_, h3⟩)

open UpperTheory.V.Z.Kato.Joint.ThetaOperator in
theorem UpperTheory.V.Z.Kato.Joint.thOp :
    UpperTheory.V.Z.Kato.Joint.ThOp := by
  intro l _ Ω _ _ _ ε X A N w j χ hS n T b hT hb i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hS' := hS
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS'
  have hψ : ∀ m, IsThB X A N l m (X.act l (sgD N l 1) b) (thN X A N l m 1 b) ∧ IsLat 1 (thN X A N l m 1 b) :=
    fun m => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl m w 1 hw (Nat.coprime_one_left N) b hb.1
  have hrel := GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw (Nat.coprime_one_left N) b hb.1
  cases T with
  | T q =>
    obtain ⟨hqp, hqNl⟩ := hT
    have hqN : q.Coprime N :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqNl)
    simp only [th, seqN, fop, Tower.op, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.EisM.To, GlobalTheory.EisM.Vo]
    have h1 := hrel.1 q hqp hqNl ((i : ℚ) / (1 : ℕ))
    rw [GlobalTheory.CyclotomicQExpansion.Api.hq_eq_uq_of_isAlgClosed hqp.pos (hψ n).2] at h1
    have h1' := cg_j hj h1
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, GlobalTheory.CyclotomicQExpansion.Api.coeff_uq hqp.pos,
      GlobalTheory.CyclotomicQExpansion.Api.coeff_vq hqp.pos, map_add, Nat.cast_one, div_one, Rat.den_natCast, if_true,
      one_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast] at h1'
    have hx : Cg n (j ((thN X A N l n q b).coeff ((i : ℚ) / q)))
        (((χ q : ℤ_[l]) : Qbar l) *
          (if q ∣ i then j ((thN X A N l n 1 b).coeff (((i / q : ℕ) : ℚ) / ((1 : ℕ) : ℚ))) else 0)) := by
      have ha := cg_j hj (hrel.2.2 q hqN ((i : ℚ) / q))
      have hc := cg_trans (cg_symm ha) (diam_cg X A N w j χ hS n q b hqN hb ((i : ℚ) / q))
      rw [one_mul] at hc
      split_ifs with hdiv
      · rwa [Nat.cast_one, div_one, Nat.cast_div hdiv (by exact_mod_cast hqp.ne_zero)]
      · rw [mul_zero]
        rwa [coeff_div_prime_eq_zero_of_not_dvd_of_isLat _ (hψ n).2 hqp hdiv, map_zero, mul_zero] at hc
    have key := cg_trans h1' (cg_lin _ _ (norm_natCast_pow_le_one q (w + 1)) hx)
    have hw2 : w + 2 - 1 = w + 1 := by omega
    simp only [Nat.cast_one, div_one, Nat.cast_mul, hw2]
    convert key using 2
    simp only [Nat.cast_one, div_one]
    ring
  | U =>
    show Cg n (j ((thN X A N l n 1 (X.heckeU l b)).coeff ((i : ℚ) / ((1 : ℕ) : ℚ))))
      (j ((thN X A N l n 1 b).coeff (((l * i : ℕ) : ℚ) / ((1 : ℕ) : ℚ))))
    have h2 := cg_j hj (hrel.2.1 ((i : ℚ) / (1 : ℕ)))
    simp only [GlobalTheory.CyclotomicQExpansion.Api.coeff_uq (Fact.out : l.Prime).pos, Nat.cast_one, div_one, Rat.den_natCast,
      if_true] at h2
    have h3 := cg_j hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hl n _ _ _ (hψ (n + 1)).1 (hψ n).1
      ((l : ℚ) * i))
    simp only [Nat.cast_one, div_one, Nat.cast_mul]
    exact cg_trans h2 h3
  | D d =>
    simp only [th, seqN, fop, Tower.op, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
      smul_eq_mul]
    exact diam_cg X A N w j χ hS n d b hT hb _

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgpTrans
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

variable {l : ℕ} [Fact l.Prime]

private theorem cgp_refl (n : ℕ) (x : Qbar l) : Cg n x x := by simp [Cg]

private theorem cgp_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cgp_add {n : ℕ} {x y x' y' : Qbar l} (h : Cg n x y) (h' : Cg n x' y') : Cg n (x + x') (y + y') := by
  unfold Cg at *
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_trans {n : ℕ} {x y z : Qbar l} (h : Cg n x y) (h' : Cg n y z) : Cg n x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_mul {n : ℕ} {a x y : Qbar l} (ha : ‖a‖ ≤ 1) (h : Cg n x y) : Cg n (a * x) (a * y) := by
  simpa using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa using ha) h

private theorem fop_cg {k n : ℕ} {χ : ℕ → Qbar l} (hχ : ∀ d, ‖χ d‖ ≤ 1) (T : Letter) {f g : ℕ → Qbar l}
    (h : ∀ i, Cg n (f i) (g i)) (i : ℕ) : Cg n (fop k l χ T f i) (fop k l χ T g i) := by
  cases T with
  | T q =>
    show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)
    unfold GlobalTheory.EisM.To GlobalTheory.EisM.Vo
    refine cgp_add (h _) (cgp_mul ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hχ q) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · split_ifs
      · exact h _
      · exact cgp_refl _ _
  | U => exact h _
  | D d => exact cgp_mul (hχ d) (h i)

theorem thP : ThP := by
  intro hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP
  set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF
  set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG
  have hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1 := fun d => by
    rw [norm_algebraMap']
    exact (χ d).2
  have hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ,
      (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧
      ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧
        G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] b' ∧
        ∀ i, Cg n (F x (th X A N j n b) i) (th X A N j n b' i) := by
    intro x hx n
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      rw [hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      refine ⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b,
        hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_,
        fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩
      rw [Tower.opV, LinearMap.baseChange_tmul]
    | one =>
      rw [map_one, map_one]
      exact ⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      refine ⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩
      obtain ⟨b', hb', e', c'⟩ := hy.2 b hb
      obtain ⟨b'', hb'', e'', c''⟩ := hx.2 b' hb'
      refine ⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩
      rw [Module.End.mul_apply, e', e'']
  have hP' : P ∈ Submodule.span (Qbar l)
      (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter)) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    obtain ⟨b', hb', e', c'⟩ := (hw x hx n).2 b hb
    rw [e', Nat.sub_zero]
    exact cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))
  | zero =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    simp only [map_zero, LinearMap.zero_apply]
    exact cgp_refl _ _
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i))
      (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
    refine ⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.sub_sub]
    exact cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuad
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hc : Continuous fun y : Ω ≃ₐ[ℚ] Ω => s⁻¹ * y := continuous_const.mul continuous_id
  have hmem : s⁻¹ * s ∈ ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with y hy
  apply h
  have hz : (s⁻¹ * y) ζ = ζ := by
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hy ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    exact this
  have : s ((s⁻¹ * y) ζ) = s ζ := by rw [hz]
  simpa using this

private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨u, rfl⟩ := hζ.isUnit (NeZero.ne M)
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf, orderOf_units]
  apply pow_eq_pow_iff_modEq.mp
  exact Units.ext (by simpa using h)

private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp only [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp at h0 ⊢
  exact h0

private theorem exists_aut_pow [IsAlgClosure ℚ Ω] {n c : ℕ} (hn : n ≠ 0) (hc : c.Coprime n) :
    ∃ s : G ℚ Ω, ∀ z : Ω, z ^ n = 1 → s z = z ^ c := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩
  haveI : NeZero n := ⟨hn⟩
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hpos).ne')
  have hprim : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.mp hζ
  have hprim' : IsPrimitiveRoot (ζ ^ c) n := hprim.pow_of_coprime c hc
  have hev : ∀ μ : Ω, IsPrimitiveRoot μ n → Polynomial.aeval μ (Polynomial.cyclotomic n ℚ) = 0 := by
    intro μ hμ
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hμ.isRoot_cyclotomic hpos
  have hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ :=
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hpos) (hev ζ hprim)
      (Polynomial.cyclotomic.monic n ℚ)
  have halg : IsAlgebraic ℚ ζ := ⟨_, Polynomial.cyclotomic_ne_zero n ℚ, hev ζ hprim⟩
  have hroot : Polynomial.aeval (ζ ^ c) (minpoly ℚ ζ) = 0 := by
    rw [← hmin]
    exact hev _ hprim'
  obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' halg hroot
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]

end

theorem UpperTheory.V.Z.Kato.Joint.chiQuad :
    UpperTheory.V.Z.Kato.Joint.ChiQuad := by
  unfold UpperTheory.V.Z.Kato.Joint.ChiQuad
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt d hd
  have hlp : Nat.Prime l := Fact.out
  have hM0 : g.M ≠ 0 := g.pos.ne'
  have hN0 : l * g.M ≠ 0 := mul_ne_zero hlp.ne_zero hM0
  haveI : NeZero g.M := ⟨hM0⟩
  haveI : NeZero (l * g.M) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l * g.M) := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l * g.M) Ω) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne')
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  have hζM : IsPrimitiveRoot (ζ ^ l) g.M := hζ.pow (Nat.pos_of_ne_zero hN0) rfl
  have hζMN : (ζ ^ l) ^ (l * g.M) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hroot : ∀ s : G ℚ Ω, ∃ i : ℕ, s (ζ ^ l) = (ζ ^ l) ^ i := by
    intro s
    have h1 : (s (ζ ^ l)) ^ g.M = 1 := by rw [← map_pow, hζM.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  choose u hu using hroot
  have hsame : ∀ s t : G ℚ Ω, s ζ = t ζ → ∀ z : Ω, z ^ (l * g.M) = 1 → s z = t z := by
    intro s t hst z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, map_pow, hst]
  have hχ : ∀ s t : G ℚ Ω, s ζ = t ζ → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      apply hK
      intro z hz
      have h2 := hsame s t hst z (by rw [pow_mul, hz, one_pow])
      rw [AlgEquiv.mul_apply, h2]
      exact t.symm_apply_apply z
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hu_eq : ∀ s t : G ℚ Ω, s ζ = t ζ → (u s : ZMod g.M) = u t := by
    intro s t hst
    apply expo_eq hζM
    rw [← hu, ← hu]
    exact hsame s t hst _ hζMN
  let f : G ℚ Ω → ℂ := fun s => ι (χ s : Qbar l) ^ 4 * g.χ (u s : ZMod g.M) ^ 2
  have hf : Continuous f := cont_of_apply ζ f (fun s t h => by simp only [f, hχ s t h, hu_eq s t h])
  have hcof : ∀ᶠ w : Pl in Filter.cofinite, ((l * g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors (I := Ideal.span {((l * g.M : ℕ) : 𝓞 ℚ)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN0
    · intro w hw
      simp only [Set.mem_setOf_eq, not_not] at hw ⊢
      exact Ideal.dvd_span_singleton.mpr hw
  have hev := hcof.and hAtt.2
  have hfeq : f = fun _ => 1 := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.mp hev) hf continuous_const ?_
    intro v hv _ B hB σ hσ
    obtain ⟨hvN, hvA⟩ := not_not.mp hv
    have hvM : ((g.M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_left _ _ h)
    have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_right _ _ h)
    have hcp := (hvA B hB).2 σ hσ
    have hdet := det_of_charpoly (a := g.a (normV v)) (d := g.χ (normV v) * (normV v : ℂ) ^ (2 * e + 1 - 1)) ι hcp
    have hfr : σ (ζ ^ l) = (ζ ^ l) ^ normV v := root_pow hM0 hB hvM hζM.pow_eq_one hσ.2
    have hus : (u σ : ZMod g.M) = normV v := expo_eq hζM (by rw [← hu, hfr])
    have hcz := cycZ_of_isFrob hvl hB hσ
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
      simp [cycBar, hcz]
    have hd2 : (dt W σ) ^ 2 = 1 := by
      have := congrArg (fun φ => φ σ) hN.det2
      simpa using this
    rw [tw_val, Matrix.det_smul] at hdet
    simp only [Fintype.card_fin, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply] at hdet
    have hw : ((↑((W σ)⁻¹) : Matrix (Fin 2) (Fin 2) (Qbar l))).det = (((dt W σ)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      change ((Matrix.GeneralLinearGroup.det ((W σ)⁻¹) : (Qbar l)ˣ) : Qbar l) = _
      rw [map_inv]
      rfl
    rw [hw] at hdet
    simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀, map_zpow₀, hcyc, map_natCast] at hdet
    set a := ι ((χ σ : (Qbar l)ˣ) : Qbar l) with ha_def
    set δ := ι ((dt W σ : (Qbar l)ˣ) : Qbar l) with hδ_def
    have ha : a ≠ 0 := (map_ne_zero ι).mpr (χ σ).ne_zero
    have hδ : δ ^ 2 = 1 := by
      have := congrArg (fun x : (Qbar l)ˣ => ι (x : Qbar l)) hd2
      simpa [hδ_def] using this
    have hδ0 : δ ≠ 0 := (map_ne_zero ι).mpr (dt W σ).ne_zero
    have hp : ((normV v : ℕ) : ℂ) ≠ 0 := by
      have h1 : ι ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (cycBar ℚ Ω l σ).ne_zero
      rwa [hcyc, map_natCast] at h1
    rw [Nat.add_sub_cancel, zpow_neg, inv_inv, zpow_natCast] at hdet
    have hχp : g.χ (normV v : ZMod g.M) = δ * a⁻¹ ^ 2 := by
      apply mul_right_cancel₀ (pow_ne_zero (2 * e) hp)
      rw [← hdet]
      field_simp
      try ring
    show a ^ 4 * g.χ (u σ : ZMod g.M) ^ 2 = 1
    rw [hus, hχp, mul_pow, hδ]
    field_simp
    try ring
  obtain ⟨c, hc1, hcd⟩ := Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl) 1 d
  have hcop : c.Coprime (l * g.M) := by
    apply Nat.Coprime.mul_right
    · have := hc1.gcd_eq
      rw [Nat.gcd_one_left] at this
      exact this
    · have := hcd.gcd_eq
      show c.gcd g.M = 1
      rw [this]
      exact hd
  obtain ⟨s, hs⟩ := exists_aut_pow (Ω := Ω) hN0 hcop
  have hχs : χ s = 1 := by
    apply hK
    intro z hz
    rw [hs z (by rw [pow_mul, hz, one_pow])]
    rw [← Nat.div_add_mod c l, pow_add, pow_mul, hz, one_pow, one_mul,
      show c % l = 1 % l from hc1, Nat.mod_eq_of_lt hlp.one_lt, pow_one]
  have hus : (u s : ZMod g.M) = d :=
    (expo_eq hζM ((hu s).symm.trans (hs _ hζMN))).trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hcd)
  have h1 := congrFun hfeq s
  simp only [f, hχs, hus, Units.val_one, map_one, one_pow, one_mul] at h1
  rw [sq] at h1
  exact mul_self_eq_one_iff.mp h1
end

