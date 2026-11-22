import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlace
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameAnyFix_map_primeToPart {M K : Type} [Monoid M] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l]
    (ι : M →* K) (x : M) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  have hl : l.Prime := Fact.out
  unfold Formalism.CyclotomicNorms.primeToPart
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0]
    have e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
      intro n hn
      subst hn
      rw [Nat.cast_one, ZMod.inv_one]
      rfl
    have e0 : l ^ (Nat.factorization 0) l = 1 := by simp
    rw [e0, e _ (by simp)]
    simp
  · set a := (orderOf x).factorization l with ha
    set m := orderOf x / l ^ a with hm
    have hmul : l ^ a * m = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : Nat.Coprime (l ^ a) m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
    have hmpos : 0 < m := Nat.ordCompl_pos l hpos.ne'
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a := by
      rw [← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 : ι x ^ m = 1 := by
      have := iterateFrobenius_inj K l a
      exact this (by simpa [iterateFrobenius_def] using h1)
    have h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast [ZMod.natCast_zmod_val]
      have := ZMod.coe_mul_inv_eq_one (l ^ a) hcop
      simpa using this
    rw [map_pow]
    have h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1 := by
      rw [pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]
    rw [h4, pow_one]

theorem tameAnyFix_isoLoc (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem tameAnyFix_not_over (D : D7) (i : D.nd.Loc) (k : Fin 2) (h : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
  intro hl
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := hl
  have hc : Nat.Coprime (D.nd.l i) (D.host.g k) := (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h
  have hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hc
  obtain ⟨a, b, hab⟩ := hc'
  apply (D.naut.plGw k v).isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)

theorem tameAnyAt_fixed : ∀ D : D7, GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  intro D hA hF i π ρ hc hr hfull hρ k hk v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨ι, hinj, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hk
  have hpol := GlobalTheory.T.inertia_charpoly_eq D hA hF i π ρ hc hr hρ _ (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)
  have hlab := D.ntypes.inertiaCharpoly_type k v _ (hfull k v)
  rw [← tameAnyFix_isoLoc D π, hlab] at hpol
  have h1 := hred _ _ hpol
  have hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ (1 : ℤ))).prod := by
    rw [D.ntypes.heckeLoc_gamma_places]
    simp only [zpow_one, tameAnyFix_map_primeToPart]
    rw [← h1, ← Matrix.charpoly_map]
    rfl
  have hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k),
      iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y →
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y := by
    intro y hy
    have h2 := hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])
    rw [D.ntypes.heckeLoc_gamma_places]
    simpa using h2
  rcases D.ntypes.chiT_tg i k v hk with h | h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩
    rw [zpow_one, tameAnyFix_map_primeToPart]
    exact hval _ h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩
    rw [zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

theorem tameFixed_of_cuspidal : ∀ D : D7, WildOne D → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  intro D hW hG hF i π ρ hc ha hfull hρ k hl v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  have hw := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hine := GlobalTheory.T.inertia_charpoly_eq D hG hF i π ρ hc ha hρ _ hw
  obtain ⟨ι, hι, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
  have hf := hfull k v
  unfold labSig at hf ⊢
  rw [isoLoc_single] at hf ⊢
  refine ⟨ι, hι, ?_, ?_⟩
  · have h1 := (hine _ (D.ntypes.tg_mem k v)).trans (D.ntypes.inertiaCharpoly_type k v _ hf)
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x => X - C (D.ntypes.teichC k x)).prod at h1
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x =>
      X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod
    set m := rts (k := k) (v := v) (D.naut.locG π _) with hm
    have hne : ∀ x ∈ m, x ≠ 0 := by
      rintro x hx rfl
      have h2 : (X : ℂ[X]) ∣ (m.map fun x => X - C (D.ntypes.teichC k x)).prod := by
        refine Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, hx, ?_⟩)
        rw [teich_zero _ (D.ntypes.teichC_inj k), map_zero, sub_zero]
      rw [← h1, ← Matrix.charpoly_map, X_dvd_iff] at h2
      have h3 := Matrix.det_eq_sign_charpoly_coeff
        (((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
      rw [h2, mul_zero] at h3
      exact (Matrix.GeneralLinearGroup.map (iotaO D.nd D.naut i) (ρ (D.ntypes.tg k v))).det_ne_zero h3
    rw [charpoly_redF, hred _ m h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [map_primeToPart ι (isOfFinOrder_of_ne_zero (hne x hx))]
  · obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 (D.naut.plGw k v))
    rw [normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)] at hφ
    refine ⟨φ, ?_⟩
    set t := D.ntypes.tg k v with ht
    have hu := wild_of_frob (D.ntypes.tg_mem k v) hφ
    have huI : (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (D.ntypes.tg_mem k v) _))
        (conj_mem_Ine hφ.1 (D.ntypes.tg_mem k v))
    set u := (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) with hudef
    have h1 := (hine u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hg : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hg _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    rw [hudef, map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
    exact h3.symm

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateDualFil

section Linear

variable {G : Type} [Group G] {LL : Type} [Field LL] (L : Type) [Field L] [Algebra LL L]
  {V : Type} [AddCommGroup V] [Module LL V] {V' : Type} [AddCommGroup V'] [Module LL V']

def extRep (ρ : Representation LL G V) : Representation L G (L ⊗[LL] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem extRep_tmul (ρ : Representation LL G V) (g : G) (a : L) (x : V) :
    extRep L ρ g (a ⊗ₜ[LL] x) = a ⊗ₜ[LL] ρ g x := rfl

theorem exists_ext_pairing [FiniteDimensional LL V] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (hm : Function.Bijective m.flip) :
    ∃ m' : L ⊗[LL] V →ₗ[L] L ⊗[LL] V' →ₗ[L] L, Function.Bijective m' ∧
      ∀ (a b : L) x y, m' (a ⊗ₜ[LL] x) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m x y) := by
  obtain ⟨v, w, hvw⟩ := GlobalTheory.DRFil.exists_dual_bases m hm
  let v' := Algebra.TensorProduct.basis L v
  let w' := Algebra.TensorProduct.basis L w
  let e := v'.equiv w'.dualBasis (Equiv.refl _)
  refine ⟨e.toLinearMap, e.bijective, fun a b x y => ?_⟩
  have h1 : ∀ i, e.toLinearMap (a ⊗ₜ[LL] v i) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m (v i) y) := by
    intro i
    have h2 : a ⊗ₜ[LL] v i = a • v' i := by
      simp [v', Algebra.TensorProduct.basis_apply, smul_tmul']
    have h3 : m (v i) y = w.repr y i := by
      conv_lhs => rw [← w.sum_repr y]
      simp only [map_sum, map_smul, hvw, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h2, map_smul, h3]
    simp only [e, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, LinearMap.smul_apply,
      Basis.dualBasis_apply, w', Algebra.TensorProduct.basis_repr_tmul]
    simp [mul_assoc]
  rw [← v.sum_repr x, tmul_sum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h4 : a ⊗ₜ[LL] (v.repr x i • v i) = algebraMap LL L (v.repr x i) • (a ⊗ₜ[LL] v i) := by
    rw [algebraMap_smul, tmul_smul]
  rw [h4, map_smul, LinearMap.smul_apply, h1, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  ring

end Linear

theorem exists_eq_bot {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ b : ℤ, ∀ a, b ≤ a → F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional k (F a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ a, finrank k (F b) ≤ finrank k (F a) :=
    ⟨Function.argmin fun a => finrank k (F a), fun a => Function.argmin_le (fun a => finrank k (F a)) a⟩
  have h1 : ∀ a, b ≤ a → F a = F b := fun a ha => Submodule.eq_of_le_of_finrank_le (hF ha) (hb a)
  refine ⟨b, fun a ha => ?_⟩
  rw [h1 a ha, eq_bot_iff]
  intro x hx
  refine hsep x fun c => ?_
  rcases le_total b c with h | h
  · rw [h1 c h]; exact hx
  · exact hF h hx

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fil_zero_add (ρ : Representation LL G V) (ρ' : Representation LL G V')
    [FiniteDimensional LL ↥(DdR PD ρ)] [FiniteDimensional LL ↥(DdR PD ρ')] (τ : K →ₐ[Qp] LL)
    (h : ∀ a, multV PD ρ' τ (-a - 1) = multV PD ρ τ a) :
    finrank LL ↥(FildR PD ρ' τ 0) + finrank LL ↥(FildR PD ρ τ 0) = finrank LL ↥(DdRE PD ρ τ) := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := GlobalTheory.Per.FilCount.exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_bot (DdR PD ρ') (FildR PD ρ' τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab))
    (fun a => le_trans inf_le_left inf_le_left)
    (fun x hx => GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hx a).2)
  let s : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ' τ (-a)) + finrank LL ↥(FildR PD ρ τ a)
  have hs : ∀ a, s (a + 1) = s a := fun a => by
    have h1 := h a
    unfold multV at h1
    rw [show -a - 1 + 1 = -a by ring, show -a - 1 = -(a + 1) by ring] at h1
    simp only [s]
    omega
  have hs0 : ∀ a, s a = s 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hs, ih]
    | pred n ih => rw [← hs, sub_add_cancel, ih]
  have h2 := hs0 (min b (-c))
  simp only [s] at h2
  rw [hb _ (min_le_left _ _), hc _ (by omega), finrank_bot, zero_add, neg_zero] at h2
  exact h2.symm

theorem descend (L : Type) [Field L] [Algebra Qp L] [Algebra LL L] [IsScalarTower Qp LL L]
    [FiniteDimensional LL L] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (H : ∀ (W : Type) [AddCommGroup W] [Module L W] [Module Qp W] [IsScalarTower Qp L W]
      [FiniteDimensional L W] (σ : Representation L G W)
      (W' : Type) [AddCommGroup W'] [Module L W'] [Module Qp W'] [IsScalarTower Qp L W']
      [FiniteDimensional L W'] (σ' : Representation L G W') (n : W →ₗ[L] W' →ₗ[L] L),
      Function.Bijective n → (∀ g x y, n (σ g x) (σ' g y) = ((cycLL PD L g : Lˣ) : L) * n x y) →
      IsDR PD σ → IsDR PD σ' ∧
        finrank L ↥(DdR PD σ' ⊓ FilV PD (LL := L) (V := W') 0) +
          finrank L ↥(DdR PD σ ⊓ FilV PD (LL := L) (V := W) 0) = finrank L ↥(DdR PD σ))
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR PD ρ) (hm : IsDual1 PD ρ ρ' m) :
    IsDR PD ρ' ∧
      finrank LL ↥(DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) = finrank LL ↥(DdR PD ρ) := by
  have hbij : Function.Bijective m.flip := by
    have hi : Function.Injective m.flip := (injective_iff_map_eq_zero _).2 fun y hy =>
      hm.2.2.1 y fun x => LinearMap.congr_fun hy x
    refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
    rw [← hm.2.2.2]
    exact Subspace.dual_finrank_eq.symm
  obtain ⟨m', hm', hm''⟩ := exists_ext_pairing L m hbij
  obtain ⟨a1, -, -, ⟨a2, -⟩, a3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V (L ⊗[LL] V) ρ (extRep L ρ)
    (TensorProduct.mk LL L V 1) (TensorProduct.isBaseChange LL V L) (fun g x => rfl)
  obtain ⟨b1, -, -, ⟨b2, -⟩, b3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V' (L ⊗[LL] V') ρ' (extRep L ρ')
    (TensorProduct.mk LL L V' 1) (TensorProduct.isBaseChange LL V' L) (fun g x => rfl)
  have hχ : ∀ g, ((cycLL PD L g : Lˣ) : L) = algebraMap LL L ((cycLL PD LL g : LLˣ) : LL) := fun g =>
    IsScalarTower.algebraMap_apply Qp LL L _
  have hinv : ∀ g x y, m' (extRep L ρ g x) (extRep L ρ' g y) = ((cycLL PD L g : Lˣ) : L) * m' x y := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
      | tmul b y =>
        rw [extRep_tmul, extRep_tmul, hm'', hm'', hm.1, map_mul, hχ]
        ring
  have hL : IsDR PD (extRep L ρ) := by
    rw [IsDR, a1, a2]; exact h
  obtain ⟨c1, c2⟩ := H _ (extRep L ρ) _ (extRep L ρ') m' hm' hinv hL
  refine ⟨by rw [IsDR, ← b1, ← b2]; exact c1, ?_⟩
  rw [← a2, ← a3, ← b3, c2]

end Period

theorem tateDual_split (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K L : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1)
    (W : Type) [AddCommGroup W] [Module ↥L.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥L.1 W]
    [FiniteDimensional ↥L.1 W] (σ : Representation ↥L.1 ↥(GK K) W)
    (W' : Type) [AddCommGroup W'] [Module ↥L.1 W'] [Module ℚ_[l] W'] [IsScalarTower ℚ_[l] ↥L.1 W']
    [FiniteDimensional ↥L.1 W'] (σ' : Representation ↥L.1 ↥(GK K) W') (n : W →ₗ[↥L.1] W' →ₗ[↥L.1] ↥L.1)
    (hn : Function.Bijective n)
    (hinv : ∀ g x y, n (σ g x) (σ' g y) = ((cycLL (P.PD K) ↥L.1 g : (↥L.1)ˣ) : ↥L.1) * n x y)
    (h : IsDR (P.PD K) σ) :
    IsDR (P.PD K) σ' ∧
      finrank ↥L.1 ↥(DdR (P.PD K) σ' ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W') 0) +
        finrank ↥L.1 ↥(DdR (P.PD K) σ ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W) 0) =
          finrank ↥L.1 ↥(DdR (P.PD K) σ) := by
  have := K.2
  obtain ⟨c1, c2⟩ := GlobalTheory.DRDual.twisted_dual_deRham l P AI T K L W σ W' σ' n 1 hn
    (fun g x y => by rw [zpow_one]; exact hinv g x y) h
  refine ⟨c1, ?_⟩
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W σ).1
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W' σ').1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  obtain ⟨d1, d2⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ
  obtain ⟨-, d3⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ'
  rw [d1, d2, d3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ =>
    finrank_fil_zero_add (P.PD K) σ σ' τ fun a => c2 τ a hcard

theorem tateDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR (P.PD K) ρ) (hm : IsDual1 (P.PD K) ρ ρ' m) :
    IsDR (P.PD K) ρ' ∧
      finrank LL ↥(DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) 0) =
          finrank LL ↥(DdR (P.PD K) ρ) := by
  obtain ⟨L, ⟨f⟩, hcard, -⟩ := GlobalTheory.exists_finExt_embedding_splitting l K LL
  have := L.2
  letI : Algebra LL ↥L.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥L.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional LL ↥L.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥L.1
  exact descend (P.PD K) ↥L.1 (tateDual_split l P AI T K L hcard) ρ ρ' m h hm

theorem main : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  intro D l _ K
  refine ⟨fun LL _ _ _ O _ _ hO A A' m h hm => ?_, fun LL _ _ _ O _ _ hO A A' m h hm => ?_⟩
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).1
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).2

end GlobalTheory.TateDualFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRham
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDualDR

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  intro D hFont hP i r hr Xs w hw n hPot X hX X' PX hD
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  obtain ⟨h1, h2, h3, h4⟩ := hD
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X'.V, ρ := X'.ρ.comp incl, cont := fun v => (X'.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW : IsCrys ((D.loc (D.nd.l i)).PD K') W.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W) (hA := hsub)).1
  have hcyc : ∀ g : ↥(GK K'),
      ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
        ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) (incl g) : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
    intro g
    have e1 := (D.loc (D.nd.l i)).PD_χ K' g
    have e2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (incl g)
    change algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((((D.loc (D.nd.l i)).PD K').χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (incl g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i])
    rw [e1, e2]
    rfl
  have hD' : IsDual1 ((D.loc (D.nd.l i)).PD K') W.ρ W'.ρ PX := by
    refine ⟨fun g v y => ?_, h2, h3, h4⟩
    rw [hcyc]
    exact h1 (incl g) v y
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (hFont (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1 W W' PX hD' hW
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X' hW'

end GlobalTheory.SummandDualDR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  first | exact @GlobalTheory.PMon.unr_of_iterate_fixed | exact GlobalTheory.PMon.unr_of_iterate_fixed | (intros; apply GlobalTheory.PMon.unr_of_iterate_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n : ℕ) (x : ℤ_[l]), x ≠ 0 → (l : Per.Acris l) ^ n ∣ ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) x) → (l - 1) * n ≤ (l - 1) * x.valuation + 2 * j := by
  first | exact @GlobalTheory.AcrisMuBound.main | exact GlobalTheory.AcrisMuBound.main | (intros; apply GlobalTheory.AcrisMuBound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChangeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachKernel_intersection_free_of_baseChange : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.WachKernel.kernel_freeA | exact GlobalTheory.WachKernel.kernel_freeA | (intros; apply GlobalTheory.WachKernel.kernel_freeA <;> assumption)
end

