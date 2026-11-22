import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0124
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0114
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0121
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import GroundTheory.AutomorphicForms.Bundle0002
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0122

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentProperties
section
open ReciprocityTheory.Ty.Fin CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem nonempty_iso_iff_equiv (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ Nonempty (Representation.Equiv τ.ρ σ.ρ) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩

theorem zIdem_act (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by
  have h := centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)
  rw [zIdem_eq_centralIdem, h]
  by_cases hc : Nonempty (τ ≅ σ)
  · rw [if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]

theorem eq_of_act (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])

theorem zIdemFacts : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ hτ
    refine ⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩
    · rw [map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
    · rw [map_mul, map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
  · intro Γ _ _ τ σ hτ hσ hne
    refine eq_of_act _ _ fun W hW => ?_
    rw [map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]
    by_cases h1 : Nonempty (τ ≅ W)
    · by_cases h2 : Nonempty (σ ≅ W)
      · exact absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne
      · simp [h2]
    · simp [h1]
  · intro Γ _ _ τ σ hτ hσ hiso
    rw [zIdem_act τ σ hτ hσ, if_pos hiso]
  · intro Γ _ _ I _ V hV hinj hex
    classical
    refine eq_of_act _ _ fun W hW => ?_
    obtain ⟨i₀, ⟨e⟩⟩ := hex W hW
    have hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) =
        if i = i₀ then (1 : Module.End ℂ W) else 0 := by
      intro i
      rw [zIdem_act (V i) W (hV i) hW]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos ⟨e.symm⟩, if_pos rfl]
      · rw [if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]
    rw [map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]
    simp

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependenceStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_independence : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.chainIndep | exact GlobalTheory.CompanionTheory.TyFin.chainIndep | (intros; apply GlobalTheory.CompanionTheory.TyFin.chainIndep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUnique
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

variable (K n d) in

def tau : Bp K n d := ∏ e, MvPolynomial.X e

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (h : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst h; rfl

theorem mon_zero (M : AddSubmonoid (Gam n d)) : mon K (0 : Gam n d) M.zero_mem = 1 := rfl

theorem mon_pow {M : AddSubmonoid (Gam n d)} (g : Gam n d) (hg : g ∈ M) (k : ℕ) :
    mon K g hg ^ k = mon K (k • g) (M.nsmul_mem hg k) := by
  induction k with
  | zero => rw [pow_zero]; exact ((mon_congr (zero_nsmul g) _ M.zero_mem).trans (mon_zero M)).symm
  | succ k ih => rw [pow_succ, ih, mon_mul]; exact mon_congr (succ_nsmul g k).symm _ _

theorem mon_prod {M : AddSubmonoid (Gam n d)} (s : Finset (E n d)) (f : E n d → Gam n d) (hf : ∀ e, f e ∈ M) :
    ∏ e ∈ s, mon K (f e) (hf e) = mon K (∑ e ∈ s, f e) (M.sum_mem fun e _ => hf e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact (mon_zero M).symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha).symm _ _

theorem poly_monomial (S : Finset (Fin d)) (k : E n d → ℕ) :
    poly n K S (∏ e, MvPolynomial.X e ^ k e) =
      mon K (∑ e, k e • oneE e) ((cone S).sum_mem fun e _ => (cone S).nsmul_mem (oneE_mem S e) (k e)) := by
  rw [map_prod]
  simp only [map_pow, poly_X, mon_pow]
  exact mon_prod _ _ _

theorem poly_tau_pow (S : Finset (Fin d)) (N : ℕ) :
    ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), (∀ e, g e = N) ∧
      poly n K S (tau K n d ^ N) = mon K g hg := by
  refine ⟨N • ∑ e, oneE e, (cone S).nsmul_mem ((cone S).sum_mem fun e _ => oneE_mem S e) N, fun e => ?_, ?_⟩
  · simp only [Pi.smul_apply, Finset.sum_apply, oneE, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul, mul_one]
  · rw [map_pow, tau, map_prod]
    simp only [poly_X]
    rw [mon_prod, mon_pow]

theorem exists_poly (S : Finset (Fin d)) (y : R0 K n d S) :
    ∃ (N : ℕ) (b : Bp K n d), poly n K S (tau K n d ^ N) * y = poly n K S b := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N₁, b₁, h₁⟩ := hf
    obtain ⟨N₂, b₂, h₂⟩ := hg
    refine ⟨N₁ + N₂, tau K n d ^ N₂ * b₁ + tau K n d ^ N₁ * b₂, ?_⟩
    rw [map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m c =>
    obtain ⟨g, hg⟩ := m
    let N : ℕ := ∑ e, (g e).natAbs
    have hN : ∀ e, 0 ≤ (N : ℤ) + g e := fun e => by
      have h1 : (g e).natAbs ≤ N := Finset.single_le_sum (f := fun e => (g e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      omega
    obtain ⟨g', hg', hc, hp⟩ := poly_tau_pow (K := K) (n := n) S N
    refine ⟨N, c • ∏ e, MvPolynomial.X e ^ ((N : ℤ) + g e).toNat, ?_⟩
    have h1 : (AddMonoidAlgebra.single ⟨g, hg⟩ c : R0 K n d S) = c • mon K g hg := by
      simp [mon]
    rw [map_smul, poly_monomial, h1, hp, mul_smul_comm, mon_mul]
    congr 1
    refine mon_congr ?_ _ _
    funext e
    have h2 : (∑ e', ((N : ℤ) + g e').toNat • (oneE e' : Gam n d)) e = ((N : ℤ) + g e).toNat := by
      simp [oneE, Finset.sum_apply, Pi.single_apply]
    rw [h2, Pi.add_apply, hc, Int.toNat_of_nonneg (hN e)]

theorem mul_injective (T : Finset (Fin d)) (N : ℕ) :
    Function.Injective fun x : R0 K n d T => poly n K T (tau K n d ^ N) * x := by
  intro x y hxy
  have hi : Function.Injective (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) :=
    AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective _)
  apply hi
  obtain ⟨g, hg, -, hp⟩ := poly_tau_pow (K := K) (n := n) T N
  have h := congrArg (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) hxy
  simp only [map_mul, hp, incl_mon] at h
  have hu : IsUnit (mon K g (AddSubmonoid.mem_top g) : Lr K n d) := by
    refine isUnit_iff_exists_inv.2 ⟨mon K (-g) (AddSubmonoid.mem_top _), ?_⟩
    rw [mon_mul]
    exact (mon_congr (add_neg_cancel g) _ _).trans (mon_zero _)
  exact hu.mul_left_cancel h

variable {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)

theorem eq_zero_of_mul {T : Finset (Fin d)} (θ' : R0 K n d T →ₐ[K] C.R T)
    (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)) (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ'))
    (N : ℕ) (z : C.R T) (hz : toR C T (phi C (tau K n d ^ N)) * z = 0) : z = 0 := by
  haveI := etale_Aa C
  haveI : Module.Flat (Bp K n d) (Aa C) := Algebra.Smooth.flat _ _
  let f : R0 K n d T →ₗ[Bp K n d] R0 K n d T := LinearMap.mulLeft (Bp K n d) (poly n K T (tau K n d ^ N))
  have hf : Function.Injective f := mul_injective T N
  have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := Aa C) f hf
  let v : Rb C T := toR C T (phi C (tau K n d ^ N))
  have key : ∀ w : TensorProduct (Bp K n d) (Aa C) (R0 K n d T),
      hb.equiv (f.lTensor (Aa C) w) = v * hb.equiv w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [map_add, hu, hu', mul_add]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      change toR C T a * θ' (poly n K T (tau K n d ^ N) * x) = toR C T (phi C (tau K n d ^ N)) * (toR C T a * θ' x)
      rw [map_mul, hθ']
      ring
  have main : ∀ z' : Rb C T, v * z' = 0 → z' = 0 := by
    intro z' hz'
    have hw : f.lTensor (Aa C) (hb.equiv.symm z') = 0 := by
      apply hb.equiv.injective
      rw [map_zero, key, LinearEquiv.apply_symm_apply]
      exact hz'
    have h3 := hl (hw.trans (map_zero _).symm)
    exact hb.equiv.symm.map_eq_zero_iff.1 h3
  exact main z hz

theorem theta_unique {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T)
    (h₁ : ∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) (h₂ : ∀ b, θ₂ (poly n K S b) = toR C T (phi C b))
    (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ')) : θ₁ = θ₂ := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨N, b, h⟩ := exists_poly S y
  have e₁ := congrArg θ₁ h
  have e₂ := congrArg θ₂ h
  rw [map_mul, h₁, h₁] at e₁
  rw [map_mul, h₂, h₂] at e₂
  refine sub_eq_zero.1 (eq_zero_of_mul C θ' hθ' hb N _ ?_)
  rw [mul_sub, e₁, e₂, sub_self]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedMissingClosedFibreEmpty
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.ClosedFibre

theorem closed_missing_closedFibre_empty : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X : Over (Spec (CommRingCat.of R))), UniversallyClosed X.hom →
  ∀ Z : Set X.left, IsClosed Z → (∀ x ∈ Z, ¬ (I ≤ (X.hom.base x).asIdeal)) → Z = ∅ := by
  intro R _ I hI X hX Z hZ h
  haveI := hI
  haveI := hX
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (X.hom.base '' Z) := X.hom.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (X.hom.base x).asIdeal (X.hom.base x).isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hsp : (X.hom.base x) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have hq : q ∈ X.hom.base '' Z := hsp.mem_closed hcl ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyq⟩ := hq
  apply h y hy
  rw [hyq]
  exact (IsAdicComplete.le_jacobson_bot (I := I)).trans (sInf_le ⟨bot_le, hm⟩)

end GlobalTheory.CompanionTheory.ClosedFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantsFiniteOfSmoothLevi
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

theorem hasFiniteLength_coinv_of_ker {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ)
    (π : Representation ℂ G U) (Φ : V →ₗ[ℂ] U) (hint : ∀ g v, Φ (τ (1, g) v) = π g (Φ v))
    (hker : LinearMap.ker Φ = twRel (τ.comp (MonoidHom.inl Γ G)) ψ) (hπ : HasFiniteLength π) :
    HasFiniteLength (coinv τ ψ) := by
  have hle : twRel (τ.comp (MonoidHom.inl Γ G)) ψ ≤ LinearMap.ker Φ := hker.ge
  have hinj : Function.Injective ((twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [← hker]
    exact hx
  let Ψ : (coinv τ ψ).IntertwiningMap π :=
    { toLinearMap := (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle
      isIntertwining' := fun g => LinearMap.ext fun x => by
        obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact hint g f }
  exact GroundTheory.Automorphic.hasFiniteLength_of_injective Ψ hinj hπ

theorem hasFiniteLength_coinv_indSnd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  intro k _ _ _ _ hI Γ W b c d _ _ _ _ _ _ _ _ _ e τ hτ ψ hfin
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ b _ (two e)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two c d)) W :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k c d).symm.toMonoidHom
  let R : Submodule ℂ W := twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ
  have hR : ∀ (m : Levi k (Two c d)) (v : W), v ∈ R → ρ m v ∈ R :=
    fun m v hv => twRel_stable τ ψ _ v hv
  let ρD : Representation ℂ (Levi k (Two c d)) (W ⧸ R) := Representation.quotient ρ R hR
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := R.mkQ, isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective R
  have hρ : IsSmooth ρ := isSmooth_comp hτ _
    ((continuous_apply false).prodMk (continuous_apply true))
  have hρD : IsSmooth ρD := (IsSubquotient.of_surjective q hq).isSmooth hρ
  haveI : FiniteDimensional ℂ (W ⧸ R) := hfin
  have hInd : HasFiniteLength (parInd (two e) ρD) :=
    hI Bool b (Two c d) (two e) (W ⧸ R) ρD hρD
      (FinitenessModel.hasFiniteLength_of_finiteDimensional ρD)
  let σ : Representation ℂ (parab k (two e)) W :=
    (twist ρ (deltaHalf k (Two c d))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : σ.IntertwiningMap ((twist ρD (deltaHalf k (Two c d))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → σ.IntertwiningMap σ := fun γ =>
    { toLinearMap := (ψ γ : ℂ)⁻¹ • τ (γ, 1)
      isIntertwining' := fun p => by
        have h := (compMap (twistMap (actFst τ γ) (deltaHalf k (Two c d))) (leviProj k (two e))).isIntertwining' p
        have h' : τ (γ, 1) ∘ₗ σ p = σ p ∘ₗ τ (γ, 1) := h
        rw [LinearMap.smul_comp, LinearMap.comp_smul, h'] }
  have hT : ∀ γ v, T γ v = (ψ γ : ℂ)⁻¹ • τ (γ, 1) v := fun _ _ => rfl
  have hψ : ∀ γ, (ψ γ : ℂ) ≠ 0 := fun γ => (ψ γ).ne_zero
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have hxR : x ∈ R := (Submodule.Quotient.mk_eq_zero R).1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z})).2 ?_ hxR
    rintro _ ⟨γ, v, rfl⟩
    have h : (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) γ v - (ψ γ : ℂ) • v =
        (ψ γ : ℂ) • (T γ v - v) := by
      rw [hT, smul_sub, smul_smul, mul_inv_cancel₀ (hψ γ), one_smul]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL b k) (parab k (two e)) (KO k b) hP
    SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k b) W (W ⧸ R) σ _ hσ
    α Γ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  refine hasFiniteLength_coinv_of_ker (indSnd e τ) ψ (parInd (two e) ρD) Φ.toLinearMap
    (fun g f => ?_) (le_antisymm ?_ ?_) hInd
  · rw [indSnd_inr]
    exact Φ.isIntertwining _ _ g f
  · intro f hf
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl Γ (GL b k))) ψ)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    have h : smIndMap (T γ) z - z = (ψ γ : ℂ)⁻¹ • (indSnd e τ (γ, 1) z - (ψ γ : ℂ) • z) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (hψ γ), one_smul]
      congr 1
      refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      show (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 x) = (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 (x * 1))
      rw [mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, z, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, f, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have h : τ (γ, 1) (f.1.1 x) - (ψ γ : ℂ) • f.1.1 x ∈ R :=
      Submodule.subset_span ⟨γ, f.1.1 x, rfl⟩
    have h2 := (Submodule.Quotient.mk_eq_zero R).2 h
    show q (τ (γ, 1) (f.1.1 (x * 1)) - (ψ γ : ℂ) • f.1.1 x) = 0
    rw [mul_one]
    exact h2

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZigzagCompat
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

universe w

variable {R : Type} [CommRing R]

def shift {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1)) (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | _ + 1, 0 => 0
  | p + 1, q + 1 => (-1 : ℤ) ^ q • B p q (x p q)

variable {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1))

theorem shift_sub (x y : ∀ p q, K.X p q) : shift B (x - y) = shift B x - shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_sub]

theorem shift_zero : shift B (0 : ∀ p q, K.X p q) = 0 := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift]

theorem shift_add (x y : ∀ p q, K.X p q) : shift B (x + y) = shift B x + shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_add]

theorem shift_sgl (p q : ℕ) (x : K.X p q) :
    shift B (K.sgl p q x) = (-1 : ℤ) ^ q • K.sgl (p + 1) (q + 1) (B p q x) := by
  funext a b
  rcases a with _ | a
  · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inl (by omega))]
    simp [shift]
  · rcases b with _ | b
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inr (by omega))]
      simp [shift]
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [shift, Pi.smul_apply, K.sgl_self]
      · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega)]
        simp only [shift]
        rw [K.sgl_ne _ (by omega)]
        simp

theorem shift_mem (m : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T m) : shift B x ∈ K.T (m + 2) := by
  intro p q h
  rcases p with _ | p
  · rfl
  · rcases q with _ | q
    · rfl
    · simp only [shift]
      rw [hx p q (by omega)]
      simp

theorem D_shift (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x)) (x : ∀ p q, K.X p q) :
    K.D (shift B x) = shift B (K.D x) := by
  funext p q
  rw [K.D_apply]
  rcases p with _ | p
  · rcases q with _ | q <;> simp [DCx.Dh, DCx.Dv, shift]
  · rcases q with _ | q
    · rcases p with _ | p <;> simp [DCx.Dh, DCx.Dv, shift]
    · have h1 : K.Dh (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ q • B p q (K.Dh x p q) := by
        rcases p with _ | p
        · simp [DCx.Dh, shift]
        · simp [DCx.Dh, shift, hh]
      have h2 : K.Dv (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ (q + 1) • B p q (K.Dv x p q) := by
        rcases q with _ | q
        · simp [DCx.Dv, shift]
        · simp only [DCx.Dv, shift, map_zsmul, hv]
          rw [pow_succ, pow_succ]
          simp
      rw [h1, h2]
      show _ = (-1 : ℤ) ^ q • B p q (K.D x p q)
      rw [K.D_apply, map_add, map_zsmul, smul_add, smul_smul, smul_smul, pow_succ, pow_succ]
      congr 2
      ring

theorem cone_zigzag_compat (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k)) (k : ℕ) :
    ∃ U : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ 2 * k → U p q = 0) ∧
      K.D U = K.sgl 0 (2 * k) (a k) - K.sgl k k (P k) := by
  induction k with
  | zero =>
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [map_zero, hP0]
    exact (sub_self _).symm
  | succ k ih =>
    obtain ⟨U, hU, hDU⟩ := ih
    refine ⟨shift B U + K.sgl 0 (2 * k + 1) (g k), fun p q h => ?_, ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, K.sgl_ne _ (by omega), add_zero]
      rcases p with _ | p
      · rfl
      · rcases q with _ | q
        · rfl
        · simp only [shift]
          rw [hU p q (by omega)]
          simp
    · rw [map_add, D_shift B hh hv, hDU, shift_sub, shift_sgl, shift_sgl, K.D_sgl, hg1, hg2, hPs, map_neg, map_zsmul]
      have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
      rw [e, one_smul, pow_zero, one_smul]
      have e2 : K.sgl 0 (2 * k + 1 + 1) (a (k + 1)) = K.sgl 0 (2 * (k + 1)) (a (k + 1)) := rfl
      rw [e2]
      abel

theorem zig_stair (F : GlobalTheory.CompanionTheory.ConeCech.DFil K) (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤)
    (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q)) (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q)
    (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k))
    (hP : P (n + 1) ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (v : K.X 0 (2 * n + 1)) (hv1 : K.dv 0 (2 * n + 1) v = a (n + 1)) (hv2 : K.dh 0 (2 * n + 1) v = 0) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P (n + 1) = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨U, hU, hDU⟩ := cone_zigzag_compat B hh hv a g P hg1 hg2 hP0 hPs (n + 1)
  refine GlobalTheory.CompanionTheory.ConeCech.stair F n hTop hV hE (P (n + 1)) hP (K.sgl 0 (2 * n + 1) v - U) ?_ ?_
  · refine sub_mem (fun p q h => K.sgl_ne _ (by omega)) (fun p q h => hU p q (by omega))
  · rw [map_sub, hDU, K.D_sgl, hv1, hv2, map_zero, zero_add, pow_zero, one_smul]
    have e2 : K.sgl 0 (2 * n + 1 + 1) (a (n + 1)) = K.sgl 0 (2 * (n + 1)) (a (n + 1)) := rfl
    rw [e2]
    abel

end GlobalTheory.CompanionTheory.ConeZig
end
end

