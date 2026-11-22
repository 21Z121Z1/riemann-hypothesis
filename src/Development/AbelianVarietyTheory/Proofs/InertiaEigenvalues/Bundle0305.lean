import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.NoGlobalInv

theorem sub_one_mem_of_pow {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {l : ℕ} (hp : l.Prime)
    (hl : (l : Λ) ∈ IsLocalRing.maximalIdeal Λ) (u : Λ) {n : ℕ} (hu : u ^ (l ^ n) = 1) :
    u - 1 ∈ IsLocalRing.maximalIdeal Λ := by
  haveI := Fact.mk hp
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue Λ)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hu]; simp
  simpa using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1

theorem exists_socle {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] (I : Ideal Λ) (S : Submodule Λ M) :
    ∀ (n : ℕ) (x : M), x ∈ S → x ≠ 0 → (∀ a ∈ I ^ n, a • x = 0) →
      ∃ y ∈ S, y ≠ 0 ∧ ∀ a ∈ I, a • y = 0 := by
  intro n
  induction n with
  | zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx
  | succ n ih =>
    intro x hS hx h
    by_cases h1 : ∀ a ∈ I, a • x = 0
    · exact ⟨x, hS, hx, h1⟩
    push Not at h1
    obtain ⟨a, ha, hax⟩ := h1
    refine ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_
    rw [smul_smul]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

theorem eq_zero_of_span {Γ O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ → Matrix (Fin r) (Fin r) O)
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) = ⊤)
    (x : Fin r → B) (hx : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ j, algebraMap O Λ a • x j = 0)
    (hs : ∀ g, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (ρ g p q) • x q = algebraMap O Λ c • x p) : x = 0 := by
  classical
  have key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (IsLocalRing.residue O) = M ∧
        ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro M
    have hM : M ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) := hρ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M h => obtain ⟨g, rfl⟩ := h; exact ⟨ρ g, rfl, hs g⟩
    | zero => exact ⟨0, by ext; simp, 0, by simp⟩
    | add M M' _ _ h h' =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨A', rfl, c', hc'⟩ := h'
      refine ⟨A + A', by ext; simp, c + c', fun p => ?_⟩
      simp only [Matrix.add_apply, map_add, add_smul, Finset.sum_add_distrib, hc, hc']
    | smul t M _ h =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      refine ⟨t • A, by ext; simp, t * c, fun p => ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]
  have key2 : ∀ A : Matrix (Fin r) (Fin r) O,
      ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro A
    obtain ⟨A', hA, c, hc⟩ := key (A.map (IsLocalRing.residue O))
    refine ⟨c, fun p => ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : A p q - A' p q ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrFun (congrFun hA p) q).symm
    have := hx _ this q
    rwa [map_sub, sub_smul, sub_eq_zero] at this
  funext b
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨a, hab⟩ := exists_ne b
  obtain ⟨c, hc⟩ := key2 (Matrix.single a b 1)
  obtain ⟨c', hc'⟩ := key2 (Matrix.single b b 1)
  have h1 := hc a
  have h2 := hc' a
  have h3 := hc' b
  simp [Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3
  rw [Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]

theorem invariants_eq_bot {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ)
    (κ : Γ →* Λˣ) (hloc : IsLocalHom (algebraMap O Λ))
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (hκ : ∀ g, ((κ g : Λˣ) : Λ) - 1 ∈ IsLocalRing.maximalIdeal Λ) (hB : Tors Λ B) :
    (repOn (twGL ρ χ) κ B).invariants = ⊥ := by
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ :=
    fun a ha hu => ha (hloc.map_nonunit a hu)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  choose n hn using fun j => hB (x j)
  obtain ⟨y, hy, hy0, hym⟩ := exists_socle (IsLocalRing.maximalIdeal Λ) _
    (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j =>
      hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))
  refine hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y
    (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)
  have hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q := fun q => by
    have := congrFun (hym _ (hκ g)) q
    rwa [Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero] at this
  have hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p :=
    congrFun (hy g) p
  rw [← hg, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]
  congr 2
  simp [twGL, scalGL, Matrix.diagonal_mul]

theorem noInv (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) (h : Setup bkP i s κ Q) : NoInv i s κ := by
  intro B _ _ _ _ hB
  have hloc := h.2.1
  have hr : 100 ≤ D.R.r := h.1.2.2.2.2.2.2
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ := fun hu =>
    hl0 (hloc.map_nonunit _ (by simpa using hu))
  refine invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB
  obtain ⟨m, hgm⟩ := h.2.2.2.2.1 g
  exact sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m)
    (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])

end GlobalTheory.NoGlobalInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EvalIdem

theorem ringHom_eq_of_unique {O A S : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing S]
    (Q : A → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : A →ₐ[O] S), (∀ a, Q a → f a = f' a) → f = f')
    (F F' : A →+* S) (h0 : ∀ o, F (algebraMap O A o) = F' (algebraMap O A o))
    (h1 : ∀ a, Q a → F a = F' a) (a : A) : F a = F' a := by
  let _ : Algebra O S := (F.comp (algebraMap O A)).toAlgebra
  have := h S ⟨F, fun _ => rfl⟩ ⟨F', fun o => (h0 o).symm⟩ h1
  exact DFunLike.congr_fun this a

theorem io_const {O T : Type} [CommRing O] [CommRing T] [Algebra O T] {n : ℕ} (f : LetA O n →ₐ[O] T) (x : O) :
    f (fun j => PowerSeries.C (algebraMap O (ZMod n → O) x j)) = algebraMap O T x := f.commutes x

theorem const_eq {O T S : Type} [CommRing O] [CommRing T] [Algebra O T] [CommRing S] {n : ℕ}
    (Q : (ZMod n → O) → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : (ZMod n → O) →ₐ[O] S),
      (∀ a, Q a → f a = f' a) → f = f')
    (f : LetA O n →ₐ[O] T) (G : T →+* S) (e : O →+* S) (i : ZMod n)
    (h0 : ∀ x, G (algebraMap O T x) = e x)
    (h1 : ∀ a, Q a → G (f (fun j => PowerSeries.C (a j))) = e (a i)) (a : ZMod n → O) :
    G (f (fun j => PowerSeries.C (a j))) = e (a i) :=
  ringHom_eq_of_unique Q h
    (G.comp (f.toRingHom.comp (RingHom.pi fun j =>
      (PowerSeries.C : O →+* PowerSeries O).comp (Pi.evalRingHom _ j))))
    (e.comp (Pi.evalRingHom _ i)) (fun x => (congrArg G (io_const f x)).trans (h0 x)) h1 a

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l}

theorem component_tmul {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) (w : Ainf l) :
    Algebra.TensorProduct.productMap ι P.ιB (β (x ⊗ₜ[ℤ_[l]] w)) = ι (x : ↥LL.1) * P.ιB (AI.ιA w) := by
  rw [hβ, Algebra.TensorProduct.productMap_apply_tmul]

theorem component_algebraMap {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) :
    Algebra.TensorProduct.productMap ι P.ιB (β (algebraMap ↥(OL LL) (RA LL) x)) = ι (x : ↥LL.1) := by
  have h1 : algebraMap ↥(OL LL) (RA LL) x = x ⊗ₜ[ℤ_[l]] (1 : Ainf l) := rfl
  rw [h1, component_tmul hβ, map_one, map_one, mul_one]

theorem component_teich {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) {K : FinExt l} (c : ↥(K0 K)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m)
    (hc : (c : Om l) ^ m = 1) (xb : OCb l) (hxb : IsTiltOf (c : Om l) m xb) :
    Algebra.TensorProduct.productMap ι P.ιB
      (β ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb)) = algebraMap ↥(K0 K) P.R.BdR c := by
  rw [component_tmul hβ, AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb, GlobalTheory.LocIota.ιB_algebraMap_Kur,
    OneMemClass.coe_one, map_one, one_mul]
  rfl

set_option maxHeartbeats 800000 in

theorem component_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  intro l _ P AI T K s LL hG Γ R I hI β hβ i ι hι o
  obtain ⟨-, -, hu⟩ := GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf l P K s LL hG Γ.emb Γ.emb_bij
  refine const_eq
    (fun a => ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
      ∀ j, ((a j : ↥(OL LL)) : ↥LL.1) = Γ.emb j c)
    (fun S _ _ f f' h => hu S f f' fun c m hm hl hc a ha => h a ⟨c, m, hm, hl, hc, ha⟩) I.io
    ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp β)
    (ι.toRingHom.comp (algebraMap ↥(OL LL) ↥LL.1)) i (component_algebraMap hβ ι) ?_ o
  rintro a ⟨c, m, hm, hl, hc, ha⟩
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have h1 := component_teich hβ ι c m hm hl hc xb hxb
  rw [← hI c m hm hl hc xb hxb a ha, ← hι, ← ha] at h1
  exact h1

end GlobalTheory.EvalIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem repIso_of_zIdem_eq_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (h : Simple τ) (h' : Simple τ') (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := by
  classical
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hco : ∀ γ, (Module.finrank ℂ τ : ℂ) * τ.character γ
      = (Module.finrank ℂ τ' : ℂ) * τ'.character γ := by
    intro γ
    have h1 := congrArg (fun z => z.coeff γ⁻¹) he
    simp only [zIdem_coeff, inv_inv] at h1
    have h2 := congrArg (fun x => (Fintype.card Γ : ℂ) * x) h1
    simp only [div_mul_eq_mul_div, mul_div_cancel₀ _ hc0, mul_div_assoc'] at h2
    simpa [FDRep.character, mul_div_cancel_left₀ _ hc0] using h2
  have hd : Module.finrank ℂ τ = Module.finrank ℂ τ' := by
    have h1 := hco 1
    rw [FDRep.char_one, FDRep.char_one] at h1
    have h2 : Module.finrank ℂ τ * Module.finrank ℂ τ
        = Module.finrank ℂ τ' * Module.finrank ℂ τ' := by exact_mod_cast h1
    exact Nat.mul_self_inj.1 h2
  have hs0 := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩] at hs0
  have hpos : (Module.finrank ℂ τ : ℂ) ≠ 0 := by
    intro h0
    have h1 : Module.finrank ℂ τ = 0 := by exact_mod_cast h0
    have : Subsingleton τ := Module.finrank_zero_iff.1 h1
    have hz : ∀ g, τ.character g = 0 := fun g => by
      have : τ.ρ g = 0 := Subsingleton.elim _ _
      simp [FDRep.character, this]
    simp [hz] at hs0
  have hch : ∀ γ, τ'.character γ = τ.character γ := fun γ => by
    have h1 := hco γ
    rw [← hd] at h1
    exact (mul_left_cancel₀ hpos h1).symm
  have hs := FDRep.char_orthonormal τ τ'
  simp only [hch] at hs
  rw [hs0] at hs
  have hne : Nonempty (τ ≅ τ') := by
    by_contra hn
    rw [if_neg hn] at hs
    exact one_ne_zero hs
  obtain ⟨i⟩ := hne
  refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
  rw [FDRep.Iso.conj_ρ i γ]
  simp [LinearEquiv.conj_apply]

end GlobalTheory.SerOSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Colim

section General

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ] {B : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]

theorem exists_fg_cocycle [CompactSpace Γ] (z : Z1 (repOn ρ κ B)) :
    ∃ B' : Submodule Λ B, B'.FG ∧ ∃ z' : Z1 (repOn ρ κ B'), ∀ g a, ((z'.1 g a : B') : B) = z.1 g a := by
  have hfin : (Set.range fun p : Γ × Fin r => z.1 p.1 p.2).Finite := by
    have hc : Continuous fun p : Γ × Fin r => z.1 p.1 p.2 :=
      continuous_prod_of_discrete_right.2 fun a => (continuous_apply a).comp z.2.1
    exact (isCompact_range hc).finite_of_discrete
  refine ⟨Submodule.span Λ _, Submodule.fg_span hfin, ⟨fun g a => ⟨z.1 g a, Submodule.subset_span ⟨(g, a), rfl⟩⟩,
    continuous_pi fun a => ((continuous_apply a).comp z.2.1).subtype_mk _, fun g h => ?_⟩, fun g a => rfl⟩
  funext a
  apply Subtype.ext
  have e := congrFun (repOn_map ρ κ (Submodule.span Λ (Set.range fun p : Γ × Fin r => z.1 p.1 p.2)).subtype g
    (fun a => ⟨z.1 h a, Submodule.subset_span ⟨(h, a), rfl⟩⟩)) a
  have e2 := congrFun (z.2.2 g h) a
  exact e2.trans (congrArg (z.1 g a + ·) e.symm)

omit [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] in
theorem repOn_eq_of_eq_one {g : Γ} (h1 : ρ g = 1) (h2 : κ g = 1) (m : Fin r → B) : repOn ρ κ B g m = m := by
  have : repOn ρ κ B g = repOn ρ κ B 1 := by simp [repOn, h1, h2]
  rw [this, map_one, Module.End.one_apply]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tgl_eq_one (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) (v : PlE D.host)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (A : ValuationSubring N.Om) (hA : IsPlaceOver A v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) A) : Tgl i s σ = 1 := by
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  have h1 : X.rhoS i s σ = 1 := h.1 v hl hg A hA σ hσ
  have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg hp A hA σ hσ
  simp [Tgl, twGL, h1, h2]

theorem selColim : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelColim bkP i s κ Q := by
  intro D N X bkP i s Λ _ _ _ κ Q hSet _ hSat B _ _ _ _ hB y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨B', hfg, z', hz⟩ := exists_fg_cocycle (Tgl i s) κ z
  have hmap : h1Map (Tgl i s) κ B'.subtype (Submodule.Quotient.mk z') = Submodule.Quotient.mk z :=
    congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => hz g a))
  refine ⟨B', hfg, Submodule.Quotient.mk z', ?_, hmap⟩
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hy v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with hl hS
  · refine hSat v hl B' B hB B'.subtype B'.injective_subtype _ ?_
    rw [← hmap] at hv
    exact hv
  · trivial
  · have hS1 : v ∉ Spl i := fun h => hS (Or.inl h)
    have hQ : v ∉ Q := fun h => hS (Or.inr h)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hv)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
    have hg : (g.1.1 : GE N) ∈ Ine (F := D.host.E) (N.plOm.1 v) := g.2
    have e : z.1 g.1.1 = repOn (Tgl i s) κ B g.1.1 m - m := hm g
    rw [repOn_eq_of_eq_one _ _ (tgl_eq_one bkP i s hSet.1.1 v hl hS1 _ (N.plOm.2 v) _ hg)
      (hSet.2.2.2.2.2.2.2 v hQ _ (N.plOm.2 v) _ hg), sub_self] at e
    show z'.1 g.1.1 = repOn (Tgl i s) κ B' g.1.1 0 - 0
    rw [LinearMap.map_zero, sub_zero]
    funext a
    apply Subtype.ext
    exact (hz g.1.1 a).trans (congrFun e a)

end GlobalTheory.SelFun.Colim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanQ
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.InvLine

theorem spanQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0) := by
  intro hT l _ P K
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ := GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K
  obtain ⟨⟨hcc, hcoc⟩, hsp⟩ := GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin
  have hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχ]; rfl
  refine ⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩
  obtain ⟨x, f, hf, hfd⟩ := hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)
  refine ⟨x, f, hf, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have e := hfd g h
  rw [← hcyc] at e
  simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← e]
  simp [charRep]

theorem exists_inv : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ (Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)) (inv : ↥Z →ₗ[LL] LL), (∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) ∧ ∀ z : ↥Z, inv z = 0 ↔ CobL (P.PD K) z.1 := by
  intro hT l _ P K LL _ _ _ O _ _ hO
  obtain ⟨z0, ⟨hz0c, hz0⟩, hspan⟩ := GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let Z : Submodule LL (↥(GK K) × ↥(GK K) → LL) :=
    { carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by
        have e1 := ha.2 g h k
        have e2 := hb.2 g h k
        simp only [Pi.add_apply]
        linear_combination e1 + e2⟩
      zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by
        have e1 := ha.2 g h k
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * e1⟩ }
  have hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0 := fun z => Iff.rfl
  let B : Submodule LL ↥Z :=
    { carrier := {z | CobL (P.PD K) z.1}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨f1, hf1, e1⟩ := ha
        obtain ⟨f2, hf2, e2⟩ := hb
        exact ⟨f1 + f2, hf1.add hf2, by rw [map_add, e1, e2]; rfl⟩
      zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩
      smul_mem' := fun c a ha => by
        obtain ⟨f1, hf1, e1⟩ := ha
        exact ⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }
  have hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1 := fun z => Iff.rfl
  let z0' : ↥Z := ⟨z0, hz0c, hz0⟩
  have hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0' := by
    intro z
    obtain ⟨x, hx⟩ := hspan z.1 z.2.1 z.2.2
    refine ⟨x, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨Z, ?_⟩
  by_cases h0 : B.mkQ z0' = 0
  · refine ⟨0, hZ, fun z => ?_⟩
    obtain ⟨x, hx⟩ := hQ z
    rw [h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    simp only [LinearMap.zero_apply, true_iff]
    exact hx
  · have htop : Submodule.span LL {B.mkQ z0'} = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨z, rfl⟩ := B.mkQ_surjective q
      obtain ⟨x, hx⟩ := hQ z
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    let φ := LinearEquiv.toSpanNonzeroSingleton LL _ _ h0
    let inv : ↥Z →ₗ[LL] LL :=
      (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ
    have hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap) :=
      φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective
    refine ⟨inv, hZ, fun z => ?_⟩
    have e1 : inv z = 0 ↔ B.mkQ z = 0 :=
      (injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)
    rw [e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GlobalTheory.InvLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalarStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertiaElement_acts_by_scalar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  first | exact @GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | exact GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | (intros; apply GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  first | exact @GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | exact GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | (intros; apply GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) * ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.epsT_pow_taylor | exact GlobalTheory.ExpImage.epsT_pow_taylor | (intros; apply GlobalTheory.ExpImage.epsT_pow_taylor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  first | exact @GlobalTheory.MemLoc.σF_root_of_unity | exact GlobalTheory.MemLoc.σF_root_of_unity | (intros; apply GlobalTheory.MemLoc.σF_root_of_unity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleFundamentalMultipleModPowStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  first | exact @GlobalTheory.UnifSpan.span_mod_pow | exact GlobalTheory.UnifSpan.span_mod_pow | (intros; apply GlobalTheory.UnifSpan.span_mod_pow <;> assumption)
end

