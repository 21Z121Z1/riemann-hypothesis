import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedSubfieldStableOfNormal
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Bridge

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem exists_finExt_of_open (U : Subgroup (Ω ≃ₐ[E] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[E] Ω))) :
    ∃ L : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK L → ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) ∈ U := by
  have hc : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) :=
    continuous_subtype_val.comp Bw.e_symm_cont
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 (hU.preimage hc)
  have h1 : (1 : GQ l) ∈ t := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      simp [U.one_mem]
    exact this
  obtain ⟨L, hL, hLt⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) t).1 (ht.mem_nhds h1)
  refine ⟨⟨L, hL⟩, fun g hg => ?_⟩
  have : g ∈ Subtype.val ⁻¹' t := hLt hg
  rw [hts] at this
  exact this

theorem rep_apply {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (g : ↥(GK Bw.Kw))
    (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

end Bridge

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Lat

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem toLL_mem (a : O) : Bw.toLL a ∈ OL Bw.LL := (Bw.eO a).2

theorem mem_stdG_OL {LL : FinExt l} {k : ℕ} (x : Fin k → ↥LL.1) :
    x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in

def bridgeLat {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K : FinExt l} (h : Bw.Kw.1 ≤ K.1) : LocLat ↥(GK K) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) where
  V := Fin m → ↥Bw.LL.1
  ρ := (Bw.rep r).comp (Subgroup.inclusion (GK_le h))
  cont := fun x => by
    have h1 : Continuous fun g : ↥(GK K) =>
        ((r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix.GeneralLinearGroup (Fin m) O) :
          Matrix (Fin m) (Fin m) O) :=
      hr.comp (Bw.e_symm_cont.comp (continuous_subtype_val.subtype_mk _))
    have h2 : Continuous (Bw.toLL) := continuous_subtype_val.comp Bw.eO_cont
    exact (h1.matrix_map h2).matrix_mulVec continuous_const
  L :=
    { T := stdG ↥(OL Bw.LL) ↥Bw.LL.1 m
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        simp only [MonoidHom.comp_apply, GlobalTheory.PotExt.rep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (toLL_mem Bw _) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective m))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥Bw.LL.1 (Fin m)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem isCrys_up (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K₁ K₂ : FinExt l} (h₁ : Bw.Kw.1 ≤ K₁.1) (h₁₂ : K₁.1 ≤ K₂.1)
    (hc : IsCrys ((LT l).PD K₁) ((Bw.rep r).comp (Subgroup.inclusion (GK_le h₁)))) :
    IsCrys ((LT l).PD K₂) ((Bw.rep r).comp (Subgroup.inclusion (GK_le (h₁.trans h₁₂)))) :=
  (hres l K₂ K₁ h₁₂ (GK_le h₁₂) Bw.LL (bridgeLat Bw r hr h₁) hc).1

end Lat

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

theorem Kur_stable (σ : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (σ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem mem_of_normal {K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (σ : GQ l) {x : Om l} (hx : x ∈ K'.1) :
    σ x ∈ K'.1 :=
  IntermediateField.normal_iff_forall_map_le'.1 hn σ ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem GKin_normal {K K' : FinExt l} (h : K.1 ≤ K'.1) (hn : Normal ℚ_[l] K'.1) : (GKin h).Normal := by
  haveI : IsGalois ℚ_[l] K'.1 := IsGalois.mk
  haveI : (GK K').Normal := (InfiniteGalois.normal_iff_isGalois K'.1).2 inferInstance
  unfold GKin
  infer_instance

theorem GKin_finiteIndex {K K' : FinExt l} (h : K.1 ≤ K'.1) : (GKin h).FiniteIndex := by
  haveI : Finite (GQ l ⧸ GK K') := Subgroup.quotient_finite_of_isOpen _ (@IntermediateField.fixingSubgroup_isOpen _ _ _ _ _ K'.1 K'.2)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  unfold GKin
  infer_instance

theorem maxUnramifiedSubfield_stable_of_normal (P : LocPrime l) {K K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (g : ↥(GK K)) (c : ↥(K0 K')) :
    ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c' := by
  have hc1 : ((c : Om l)) ∈ K'.1 := c.2.1
  have hc2 : ((c : Om l)) ∈ MaximalUnramifiedExtension l := c.2.2
  refine ⟨⟨(g : GQ l) c, mem_of_normal hn _ hc1, Kur_stable _ hc2⟩, ?_⟩
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc2⟩ ⟨(g : GQ l) c, Kur_stable _ hc2⟩ rfl

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

theorem main : ∀ (D : D7) (P : Pend D), ElementDenominator.adm12 D → ∀ (i : D.nd.Loc) (k : Fin 2)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0) →
  ∀ (ι : Type) [Finite ι] (n : ℕ) (R : ι → (GE D.nd →* GL (Fin n) (D.nd.O i))) (n₀ : ℕ)
    (R₀ : GE D.nd →* GL (Fin n₀) (D.nd.O i)),
  (∀ j, Continuous fun g => ((R j g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) →
  (Continuous fun g => ((R₀ g : GL (Fin n₀) (D.nd.O i)) : Matrix (Fin n₀) (Fin n₀) (D.nd.O i))) →
  (∀ j, Br.IsPotCrysW D.loc D.nbr i w hw (R j)) → Br.IsPotCrysW D.loc D.nbr i w hw R₀ →
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
          algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
    (∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((R j).comp (decS D.nd w)))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R₀.comp (decS D.nd w))) ∧
    ∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
  intro D P hadm i k w hw Y hY ι _ n R n₀ R₀ hRc hR₀c hRp hR₀p
  unfold Br.IsPotCrysW LocBridge.IsPotCrysW at hRp hR₀p
  choose Kj hj hcj using hRp
  obtain ⟨K₀', h₀, hc₀⟩ := hR₀p
  have hLy : ∀ y : ↥Y, ∃ L : FinExt (D.nd.l i), ∀ g : ↥(GK (D.nbr i w hw).Kw), (g : GQ (D.nd.l i)) ∈ GK L →
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
    intro y
    obtain ⟨U, hU, hUo⟩ := P.om_open k w y (hY y y.2)
    obtain ⟨L, hL⟩ := exists_finExt_of_open (D.nbr i w hw) U hU
    exact ⟨L, fun g hg hI => hUo _ (hL g hg) hI⟩
  choose Ly hLy using hLy
  haveI : ∀ j, FiniteDimensional ℚ_[D.nd.l i] (Kj j).1 := fun j => (Kj j).2
  haveI : ∀ y, FiniteDimensional ℚ_[D.nd.l i] (Ly y).1 := fun y => (Ly y).2
  haveI := (D.nbr i w hw).Kw.2
  haveI := K₀'.2
  let M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    (D.nbr i w hw).Kw.1 ⊔ K₀'.1 ⊔ (⨆ j, (Kj j).1) ⊔ (⨆ y, (Ly y).1)
  haveI : FiniteDimensional ℚ_[D.nd.l i] M := by infer_instance
  let K' : FinExt (D.nd.l i) := ⟨IntermediateField.normalClosure ℚ_[D.nd.l i] M (Om (D.nd.l i)), inferInstance⟩
  have hMK : M ≤ K'.1 := IntermediateField.le_normalClosure M
  have hn : Normal ℚ_[D.nd.l i] K'.1 := normalClosure.normal _ _ _
  have h : (D.nbr i w hw).Kw.1 ≤ K'.1 := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hMK
  have h0K : K₀'.1 ≤ K'.1 := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hMK
  refine ⟨K', h, GKin_normal h hn, GKin_finiteIndex h, maxUnramifiedSubfield_stable_of_normal _ hn, fun j => ?_, ?_, ?_⟩
  · have hjK : (Kj j).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun j => (Kj j).1) j).trans (le_sup_right.trans le_sup_left)) hMK
    refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ ((hRc j).comp continuous_subtype_val) (hj j) hjK (hcj j)
  · refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ (hR₀c.comp continuous_subtype_val) h₀ h0K hc₀
  · intro y hy g hg hI
    have hyK : (Ly ⟨y, hy⟩).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun y => (Ly y).1) ⟨y, hy⟩).trans le_sup_right) hMK
    exact hLy ⟨y, hy⟩ g (GK_le hyK (Subgroup.mem_subgroupOf.1 hg)) hI

end GlobalTheory.PotExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.ResR

open Matrix

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem resGL_mul_inv_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (resMat n ω).map f * (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.mul_inv, map_one]

theorem resGL_inv_mul_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f * (resMat n ω).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.inv_mul, map_one]

theorem resMat_mulVec_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) (v : n × Fin r → S) (i : n) (m : Fin r) :
    ((resMat n ω).map f *ᵥ v) (i, m) = ∑ k, f (fr l m (ω k)) * v (i, k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, resMat_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

theorem sum_fr_mul_eq_iter (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (m : ℕ) (i : n) :
    ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * u (i, k) = P.φB^[m] (a i) := by
  have h := congrFun hu (i, ⟨m % r, Nat.mod_lt _ hr⟩)
  rw [resMat_mulVec_apply] at h
  simp only [fr_mod (hω _)] at h
  rw [h]
  exact Function.IsPeriodicPt.iterate_mod_apply (ha i) m

theorem phi_fix_of_res (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (hdet : (frobMat ω).det ≠ 0)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (j : n × Fin r) : P.φB (u j) = u j := by
  set d : n × Fin r → P.R.B := fun j => P.φB (u j) - u j with hd
  have hz : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ d = 0 := by
    funext ⟨i, m⟩
    rw [resMat_mulVec_apply]
    have h1 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1)) i
    have h2 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1) + 1) i
    have e : m + (r - 1) + 1 = (m : ℕ) + r := by omega
    rw [Function.iterate_succ_apply', ← h1, map_sum] at h2
    simp only [map_mul, phiB_algebraMap, ← fr_one, ← fr_add] at h2
    rw [show 1 + ((m : ℕ) + (r - 1)) = (m : ℕ) + r by omega, e] at h2
    simp only [fr_add, hω] at h2
    simp only [hd, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    rw [h2, sub_self]
  have : d = 0 := by
    rw [← Matrix.one_mulVec d, ← resGL_inv_mul_map n ω hdet, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  exact sub_eq_zero.1 (congrFun this j)

def tzGL {N : Type} [Fintype N] [DecidableEq N] (e : N → ℤ) : GL N P.R.BdR where
  val := Matrix.diagonal fun j => tz P (e j)
  inv := Matrix.diagonal fun j => tz P (-e j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]

theorem iota_q_eq (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR)
    (e : n × Fin r → ℤ) (A₀ : GL (n × Fin r) P.R.B) (W₀ : GL (n × Fin r) P.R.BdR)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) =
      (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) :
    ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB *
      ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB *
      (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
  set G : GL (n × Fin r) P.R.BdR := Units.map ((P.ιB : P.R.B →+* P.R.BdR).mapMatrix).toMonoidHom A₀ with hGdef
  set kp : GL (n × Fin r) P.R.BdR := Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
    Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) with hkp
  have hG : G = kp⁻¹ * blockGL U * tzGL P e * W₀ := by
    apply Units.ext
    rw [hGdef]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Units.val_mul]
    rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (P.ιB : P.R.B →+* P.R.BdR) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) from rfl, hA]
    rfl
  have h1 : ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB =
      ((G⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hGdef, ← map_inv, Units.coe_map]
    rfl
  have h2 : ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB = ((kp⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hkp, ← map_inv, Units.coe_map, Matrix.map_map]
    ext i j
    simp [iota_kur]
  have h3 : (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((blockGL U * tzGL P e : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
  rw [h1, h2, Matrix.mul_assoc, h3, ← Units.val_mul, ← Units.val_mul, hG]
  congr 1
  group

theorem mem_span_colv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B),
    (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) →
    ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ →
    (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) →
    ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  intro l _ P r hr ω hω hdet n _ _ U x y A₀ hφ W₀ hW₀ hA a hLat
  obtain ⟨ha, hw⟩ := hLat
  choose w hw0 hwe using hw
  set pB : Matrix (n × Fin r) (n × Fin r) P.R.B := (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpB
  set pI : Matrix (n × Fin r) (n × Fin r) P.R.B :=
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
      (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpI
  set V : n × Fin r → P.R.B := fun j => P.φB^[j.2] (a j.1) with hV
  set u : n × Fin r → P.R.B := pI *ᵥ V with hu
  have hpu : pB *ᵥ u = V := by
    rw [hu, Matrix.mulVec_mulVec, hpB, hpI, resGL_mul_inv_map, Matrix.one_mulVec]
  set Ai : Matrix (n × Fin r) (n × Fin r) P.R.B := ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    with hAi
  set q : n × Fin r → P.R.B := Ai *ᵥ u with hq

  have hAφ : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB = A₀ := Matrix.ext fun i j => hφ i j
  have hAiφ : Ai.map (P.φB : P.R.B →+* P.R.B) = Ai := by
    have h1 : Ai.map (P.φB : P.R.B →+* P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) = 1 := by
      conv_lhs => rw [← hAφ]
      rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB =
          ((P.φB : P.R.B →+* P.R.B).mapMatrix (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)) from rfl,
        show Ai.map (P.φB : P.R.B →+* P.R.B) = (P.φB : P.R.B →+* P.R.B).mapMatrix Ai from rfl, ← map_mul, hAi,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    calc Ai.map (P.φB : P.R.B →+* P.R.B)
        = Ai.map (P.φB : P.R.B →+* P.R.B) * ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) * Ai) := by
          rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = Ai := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have huφ : ∀ j, P.φB (u j) = u j := phi_fix_of_res P hr ω hω hdet a ha u hpu
  have hqφ : ∀ c, P.φB (q c) = q c := by
    intro c
    have := RingHom.map_mulVec (P.φB : P.R.B →+* P.R.B) Ai u c
    rw [hAiφ] at this
    change P.φB (q c) = _ at this
    rw [this, hq]
    congr 1
    funext j
    exact huφ j

  set wt : n × Fin r → P.R.BdR := fun j => w j.2 j.1 with hwt
  have hιV : (fun j => P.ιB (V j)) = ((blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))) *ᵥ wt := by
    funext ⟨i, m⟩
    have h := congrFun (hwe m) i
    change P.ιB (P.φB^[m] (a i)) = _
    have hd : ∀ (v w : n × Fin r → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    have hd' : ∀ (v w : n → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    rw [show P.ιB (P.φB^[m] (a i)) = ev P m (a i) from rfl, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hd, hd']
    simp only [Matrix.mulVec, dotProduct, blockGL, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, hwt]
    rw [Finset.sum_comm, Finset.sum_eq_single m]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have hιq : (fun c => P.ιB (q c)) = ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ wt := by
    funext c
    have e1 := RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) Ai u c
    have e2 : (fun j => P.ιB (u j)) = (pI.map (P.ιB : P.R.B →+* P.R.BdR)) *ᵥ (fun j => P.ιB (V j)) := by
      funext j
      exact RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) pI V j
    change P.ιB (q c) = _ at e1
    rw [e1]
    change (Ai.map P.ιB *ᵥ (fun j => P.ιB (u j))) c = _
    rw [e2, hιV, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← iota_q_eq P ω hdet U (fun j : n × Fin r => eps x y (j.2, j.1)) A₀ W₀ hA]
    simp only [Matrix.mul_assoc]
    rfl
  have hqF : ∀ c, P.ιB (q c) ∈ Fil P 0 := by
    intro c
    rw [show P.ιB (q c) = (fun c => P.ιB (q c)) c from rfl, hιq]
    exact Fil_sum fun j _ => Fil_mul_left (hW₀.2 c j) (hw0 j.2 j.1)
  choose cq hcq using fun c => fund P (hqφ c) (hqF c)

  have hAq : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) *ᵥ q = u := by
    rw [hq, Matrix.mulVec_mulVec, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have haeq : a = ∑ c, cq c • colv P ω A₀ c := by
    funext i
    have h0 := sum_fr_mul_eq_iter P hr ω hω a ha u hpu 0 i
    simp only [fr_zero, Function.iterate_zero, id] at h0
    rw [← h0, ← hAq]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [Algebra.smul_def, hcq, colv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [haeq]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))

end GlobalTheory.PMon.ResR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V], Function.Surjective (monV P ℚ_[l] V) := by
  first | exact @GlobalTheory.PMon.monV_surjective_onto | exact GlobalTheory.PMon.monV_surjective_onto | (intros; apply GlobalTheory.PMon.monV_surjective_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_of_ordIs_ext : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = ramificationIndex F L * e ∧ ramificationIndex F L = Nat.card ↥(lowerRamificationGroup F L 0) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E h
  unfold OrdIs at h ⊢
  have hmap := addVal_algebraMap_integer F L (p : 𝒪[F])
  rw [map_natCast] at hmap
  rw [hmap] at h
  have hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')] at h
    exact ENat.coe_ne_top E h.symm
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero F L).symm⟩
  rw [← he] at h
  exact_mod_cast h.symm

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCasesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFilStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_teichmullerRoot_taylor_modFil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  first | exact @GlobalTheory.ExpImage.PolyTaylor.poly_taylor | exact GlobalTheory.ExpImage.PolyTaylor.poly_taylor | (intros; apply GlobalTheory.ExpImage.PolyTaylor.poly_taylor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R →
    (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  intro G _ R A B n _ h
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [if_neg ((h t).1 (Finset.mem_range.1 ht))]
  · intro t ht
    rw [Function.mem_support] at ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hn
    exact ht (if_pos (not_not.1 (mt (h t).2 hn)))

end GlobalTheory.PMon.Ram
end

