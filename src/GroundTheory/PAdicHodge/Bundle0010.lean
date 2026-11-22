import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenFrob
import GroundTheory.PAdicHodge.SlopeRobbaPure

-- bundled from GroundTheory.PAdicHodge.BCrisEigenChar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenChar

open GroundTheory.LocalField EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

theorem algebraMap_padic_cp_injective : Function.Injective (algebraMap ℚ_[p] ℂ_[p]) :=
  (algebraMap ℚ_[p] ℂ_[p]).injective

theorem isometry_algebraMap_padic_cp : Isometry (algebraMap ℚ_[p] ℂ_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' ℂ_[p])

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem eq_of_mul_eq {x : ℂ_[p]} (hx : x ≠ 0) {q q' : ℚ_[p]}
    (h : algebraMap ℚ_[p] ℂ_[p] q * x = algebraMap ℚ_[p] ℂ_[p] q' * x) : q = q' :=
  algebraMap_padic_cp_injective (mul_right_cancel₀ hx h)

theorem exists_eigenChar {x : ℂ_[p]} (hx : x ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) :
    ∃ ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ, Continuous ψ ∧
      ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x := by
  choose q hq using h
  let ψ₀ : Gal(PadicAlgCl p/K) →* ℚ_[p] :=
    { toFun := q
      map_one' := eq_of_mul_eq hx (by rw [← hq, one_smul, map_one, one_mul])
      map_mul' := fun σ τ => eq_of_mul_eq hx (by
        rw [← hq, mul_smul, hq τ, smul_mul', gal_smul_algebraMap, hq σ, map_mul]
        ring) }
  have hcont₀ : Continuous ψ₀ := by
    rw [isometry_algebraMap_padic_cp.isEmbedding.continuous_iff]
    have e : (algebraMap ℚ_[p] ℂ_[p]) ∘ ψ₀ = fun σ => (σ • x) * x⁻¹ := by
      funext σ
      simp only [Function.comp_apply]
      change algebraMap ℚ_[p] ℂ_[p] (q σ) = _
      rw [hq σ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [e]
    exact (continuous_id.smul continuous_const).mul continuous_const
  refine ⟨ψ₀.toHomUnits, ?_, fun σ => hq σ⟩
  rw [Units.continuous_iff]
  refine ⟨hcont₀, ?_⟩
  have e : (fun σ => (((ψ₀.toHomUnits σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) = ψ₀ ∘ fun σ => σ⁻¹ := by
    funext σ
    rw [← map_inv]
    rfl
  rw [e]
  exact hcont₀.comp continuous_inv

theorem norm_eigen_eq_one {x : ℂ_[p]} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)} {q : ℚ_[p]}
    (h : σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) : ‖q‖ = 1 := by
  have h1 := norm_smul_gal σ x
  rw [h, norm_mul, norm_algebraMap'] at h1
  exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx) (h1.trans (one_mul _).symm)

def galRes {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Gal(PadicAlgCl p/L) →* Gal(PadicAlgCl p/K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun k => σ.commutes ⟨(k : PadicAlgCl p), hKL k.2⟩)
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

theorem galRes_apply {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (y : PadicAlgCl p) : galRes hKL σ y = σ y := rfl

theorem galRes_smul {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (x : ℂ_[p]) : galRes hKL σ • x = σ • x := rfl

theorem exists_fixingSubgroup_of_finite_image (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ) (hψ : Continuous ψ)
    (S : Set Gal(PadicAlgCl p/K)) (hfin : (ψ '' S).Finite) :
    ∃ E : IntermediateField K (PadicAlgCl p), FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, σ ∈ S → ψ σ = 1 := by
  set F := ψ '' S \ {1} with hF
  have hFc : IsClosed F := (hfin.subset Set.sdiff_subset).isClosed
  have hO : ψ ⁻¹' Fᶜ ∈ nhds (1 : Gal(PadicAlgCl p/K)) := by
    refine (hFc.isOpen_compl.preimage hψ).mem_nhds ?_
    simp [hF]
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) _).1 hO
  refine ⟨E, hE, fun σ hσ hS => ?_⟩
  by_contra hne
  exact hsub hσ ⟨⟨σ, hS, rfl⟩, hne⟩

theorem mem_inertia_of_degree {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) :
    ∀ u ∈ unramifiedClosure p, σ u = u := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  have hroot : ∀ ζ ∈ primeToPRoots p, σ ζ = ζ := by
    rintro ζ ⟨m, hm, hcop, hζ⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_iff.2 ⟨m, ?_, hζ⟩))
    intro h0
    rw [CharP.cast_eq_zero_iff _ p] at h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop.symm h0
  intro u hu
  induction hu using IntermediateField.adjoin_induction with
  | mem x hx => exact hroot x hx
  | algebraMap q =>
    exact σ.commutes (algebraMap ℚ_[p] L q)
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_twist_of_unramified {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L] {x : ℂ_[p]} (hx : x ≠ 0) (ψ : Gal(PadicAlgCl p/L) →* ℚ_[p]ˣ)
    (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ c : (AInf ℂ_[p] p)ˣ, ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
      (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  have := isSepClosure_padicAlgCl (L := L)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := L) (Ω := PadicAlgCl p)
    (Multiplicative.ofAdd 1)
  have hw : ‖((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := norm_eigen_eq_one hx (hψx σ₀)
  set w : ℤ_[p]ˣ := PadicInt.mkUnits hw with hwdef
  have hwcoe : ((w : ℤ_[p]) : ℚ_[p]) = ((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p]) := rfl
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (L := L)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := L) w
  set cA := wittToAInf (b : WittVector p (Fpbar p)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[p]) p
  set xc : ℂ_[p] := ((θ cA : normInteger ℂ_[p]) : ℂ_[p]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[p] ℂ_[p] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz0 : ∀ σ, (z σ : ℚ_[p]) ≠ 0 := fun σ h => by
    have := norm_eigen_eq_one hxc (hxcσ σ)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set X := x ^ f * xc⁻¹ with hXdef
  have hX : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero hxc)
  have hXσ : ∀ σ, σ • X = algebraMap ℚ_[p] ℂ_[p]
      (((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹) * X := fun σ => by
    rw [hXdef, ← galCp_apply, map_mul, map_pow, map_inv₀, galCp_apply, galCp_apply, hψx σ, hxcσ σ,
      map_mul, map_pow, map_inv₀]
    have hz' : algebraMap ℚ_[p] ℂ_[p] (z σ : ℚ_[p]) ≠ 0 :=
      (map_ne_zero_iff _ algebraMap_padic_cp_injective).2 (hz0 σ)
    field_simp
    ring
  obtain ⟨ρ, hρc, hρ⟩ := exists_eigenChar hX (fun σ => ⟨_, hXσ σ⟩)
  have hρeq : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) =
      ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹ := fun σ =>
    eq_of_mul_eq hX ((hρ σ).symm.trans (hXσ σ))
  have hz₀ : (z σ₀ : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → (z σ : ℚ_[p]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt p (z σ) * cA = IsPerfectoidField.padicIntToWitt p 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  let ρC : Gal(PadicAlgCl p/L) →* ℂ_[p] :=
    (algebraMap ℚ_[p] ℂ_[p]).toMonoidHom.comp ((Units.coeHom ℚ_[p]).comp ρ)
  have hρC : Continuous ρC :=
    isometry_algebraMap_padic_cp.continuous.comp (Units.continuous_val.comp hρc)
  have hρ1 : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 → ρC σ = 1 := fun σ h => by
    change algebraMap ℚ_[p] ℂ_[p] ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1
    rw [h, map_one]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (hρ1 σ₀ (by rw [hρeq, hz₀, hwcoe, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))]))
    (fun σ hσ => hρ1 σ (by rw [hρeq, hzI σ hσ, hI σ hσ, Units.val_one, one_pow, inv_one, mul_one]))
  refine ⟨f, hf, hcu.unit, fun σ => ⟨z σ, ?_, hz σ⟩⟩
  have h1 : ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 := algebraMap_padic_cp_injective (by
    rw [map_one]
    exact hall σ)
  rw [hρeq] at h1
  exact (mul_inv_eq_one₀ (hz0 σ)).1 h1 |>.symm

end EigenChar

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SlopeFiltration
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

namespace PhiModule

universe u

variable {F : FrobeniusLift K}
variable {M : Type u} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

variable (F) in

def IsSemistableSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : Prop :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  IsSemistable F (subquot Φ N N' h h')

variable (F) in

def degSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : ℤ :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  deg F.unitOrd (subquot Φ N N' h h')

variable (F) in

structure HNFiltration (Φ : M →ₛₗ[F.phi] M) where

  length : ℕ

  N : ℕ → Submodule (Robba K) M

  slope : ℕ → ℚ
  N_zero : N 0 = ⊥
  N_of_le : ∀ i, length ≤ i → N i = ⊤
  lt_succ : ∀ i, i < length → N i < N (i + 1)
  stable : ∀ i, IsStable Φ (N i)
  saturated : ∀ i, Module.IsTorsionFree (Robba K) (M ⧸ N i)
  semistable : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    IsSemistableSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1))
  deg_eq : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    (degSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1)) : ℚ) =
      slope i * finrank (Robba K) (N (i + 1) ⧸ inSub (N i) (N (i + 1)))
  slope_lt : ∀ i j, i < j → j < length → slope i < slope j

theorem finrank_subquot_pos {N N' : Submodule (Robba K) M} (hlt : N < N')
    [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.IsTorsionFree (Robba K) (M ⧸ N')] :
    0 < finrank (Robba K) (N' ⧸ inSub N N') := by
  have := free_subquot (N := N) (N' := N')
  have := finite_subquot (N := N) (N' := N')
  have := isTorsionFree_subquot (N := N) (N' := N')
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨x, hx, hxN⟩ := SetLike.exists_of_lt hlt
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, fun h0 => hxN ?_⟩
  rw [Submodule.Quotient.mk_eq_zero] at h0
  exact h0

def HNFiltration.toSlopeFiltration {Φ : M →ₛₗ[F.phi] M}
    (hss : ∀ (M' : Type u) [AddCommGroup M'] [Module (Robba K) M'] [Module.Free (Robba K) M']
      [Module.Finite (Robba K) M'] (Φ' : M' →ₛₗ[F.phi] M'), IsSemistable F Φ' →
      0 < finrank (Robba K) M' → IsPure F Φ' ((deg F.unitOrd Φ' : ℚ) / finrank (Robba K) M'))
    (S : HNFiltration F Φ) : SlopeFiltration F Φ where
  length := S.length
  N := S.N
  slope := S.slope
  N_zero := S.N_zero
  N_of_le := S.N_of_le
  lt_succ := S.lt_succ
  stable := S.stable
  saturated := S.saturated
  pure i hi := by
    have := S.saturated i
    have := S.saturated (i + 1)
    have := free_subquot (N := S.N i) (N' := S.N (i + 1))
    have := finite_subquot (N := S.N i) (N' := S.N (i + 1))
    have hpos := finrank_subquot_pos (S.lt_succ i hi)
    have hp := hss _ _ (S.semistable i hi) hpos
    have hdeg := S.deg_eq i hi
    have hr : (finrank (Robba K) (S.N (i + 1) ⧸ inSub (S.N i) (S.N (i + 1))) : ℚ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    change IsPure F (subquot Φ (S.N i) (S.N (i + 1)) (S.stable i) (S.stable (i + 1))) (S.slope i)
    change (degSubquot F Φ _ _ _ _ : ℚ) = _ at hdeg
    unfold degSubquot at hdeg
    rw [hdeg, mul_div_assoc, div_self hr, mul_one] at hp
    exact hp
  slope_lt := S.slope_lt

theorem nonempty_slopeFiltration_of {Φ : M →ₛₗ[F.phi] M}
    (hss : ∀ (M' : Type u) [AddCommGroup M'] [Module (Robba K) M'] [Module.Free (Robba K) M']
      [Module.Finite (Robba K) M'] (Φ' : M' →ₛₗ[F.phi] M'), IsSemistable F Φ' →
      0 < finrank (Robba K) M' → IsPure F Φ' ((deg F.unitOrd Φ' : ℚ) / finrank (Robba K) M'))
    (hHN : Nonempty (HNFiltration F Φ)) : Nonempty (SlopeFiltration F Φ) :=
  hHN.map (HNFiltration.toSlopeFiltration hss)

end PhiModule

end GroundTheory.PAdicHodge
end
end

