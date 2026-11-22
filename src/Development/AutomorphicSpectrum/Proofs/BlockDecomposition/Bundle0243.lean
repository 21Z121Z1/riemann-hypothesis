import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0172
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrime
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.TensOne

open TensorProduct

section Generic

variable {R S W C : Type} [CommRing R] [CommRing S] [CommRing W] [CommRing C]
  [Algebra R S] [Algebra R W] [Algebra R C]

theorem tmul_mul_natCast_mem (p : ℕ) (e : S) (x : W) :
    (e * (p : S)) ⊗ₜ[R] x ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm
  have : (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem tmul_natCast_mul_mem (p : ℕ) (e : S) (x : W) :
    e ⊗ₜ[R] (x * (p : W)) ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W) :=
    (map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm
  have : e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gsum (d : ℕ → S) (w : ℕ →₀ W) : S ⊗[R] W := w.sum fun k x => d k ⊗ₜ[R] x

theorem gsum_add (d : ℕ → S) (w w' : ℕ →₀ W) :
    (gsum d (w + w') : S ⊗[R] W) = gsum d w + gsum d w' :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _

theorem exists_gsum (p : ℕ) (d : ℕ → S)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (z : S ⊗[R] W) : ∃ w : ℕ →₀ W, z - gsum d w ∈ Ideal.span {(p : S ⊗[R] W)} := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [gsum]⟩
  | tmul a x =>
    obtain ⟨s, c, hc⟩ := hsurj a
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩
    have h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) =
        (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x := by
      rw [gsum, ← Finsupp.sum_finset_sum_index (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.sub_tmul, ← he]
    exact tmul_mul_natCast_mem p e x
  | add x y hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    refine ⟨w + w', ?_⟩
    have : x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w') := by
      rw [gsum_add]; ring
    rw [this]
    exact add_mem hw hw'

theorem generic (p : ℕ) (d : ℕ → S) (r0 : R) (f : S →ₐ[R] C) (g : W →ₐ[R] C)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (hv : ∀ k, algebraMap R S r0 * d k ∈ Ideal.span {(p : S)})
    (hK : ∀ (s : Finset ℕ) (w : ℕ → W), ∑ k ∈ s, f (d k) * g (w k) = 0 →
      ∀ k ∈ s, w k ∈ Ideal.span {algebraMap R W r0, (p : W)})
    (hC : (p : C) = 0) (z : S ⊗[R] W)
    (hz : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = 0) :
    z ∈ Ideal.span {(p : S ⊗[R] W)} := by
  obtain ⟨w, hw⟩ := exists_gsum p d hsurj z
  have hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hw
    rw [← hy, map_mul, map_natCast, hC, mul_zero]
  rw [map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum] at hL
  have hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0 := by
    rw [← hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  have hk := hK _ _ hsum
  have hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)} := by
    refine Ideal.sum_mem _ fun k hks => ?_
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hk k hks)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hv k)
    have h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u := by
      rw [he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    change d k ⊗ₜ[R] (w k) ∈ _
    rw [← huv, TensorProduct.tmul_add, h1]
    exact add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)
  have := add_mem hw hG
  rwa [sub_add_cancel] at this

end Generic

section Specific

variable {l : ℕ} [Fact l.Prime]

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.1
  tf := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.2

theorem isBase_base : IsBase l (base (l := l)) := Function.bijective_id

def d (k : ℕ) : Acris l := AdicCompletion.of _ _ (ACris.dpowZero (xi0_mem (l := l)) k)

theorem cris_d (A : PAlg l) (n k : ℕ) : A.cris n (d k) = A.dxi n k := by
  rw [d, cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)

theorem sW_base (x : Ainf l) : (base (l := l)).sW x = x := wmap_id x

theorem cris_teich (a : Ob l) :
    (base (l := l)).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l a)) =
      (base (l := l)).aTo1 a := by
  have h1 := (base (l := l)).aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h1
  have h2 := (base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)
  rw [sW_base] at h2
  rw [h1]
  exact h2

theorem mem_of_cris (a : Acris l) (h : (base (l := l)).cris 1 a = 0) : a ∈ Ideal.span {(l : Acris l)} := by
  have := (RingHom.mem_ker).2 h
  rwa [((GlobalTheory.T.period_ring_comparison_of_base base isBase_base).2 1).2, pow_one] at this

theorem hsurj (a : Acris l) : ∃ (s : Finset ℕ) (c : ℕ → Ainf l),
    a - ∑ k ∈ s, algebraMap (Ainf l) (Acris l) (c k) * d (l * k) ∈ Ideal.span {(l : Acris l)} := by
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).1 ((base (l := l)).cris 1 a)
  refine ⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩
  have e : (base (l := l)).expand c =
      ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl
  rw [map_sub, ← hc, e, sub_eq_zero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cris_teich, cris_d]

def r0 : Ainf l := WittVector.teichmuller l (pFlat l ^ l)

theorem hv (k : ℕ) : algebraMap (Ainf l) (Acris l) (r0 (l := l)) * d k ∈ Ideal.span {(l : Acris l)} := by
  refine mem_of_cris _ ?_
  rw [map_mul, r0, cris_teich, cris_d]
  exact (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).2.2.2 k

theorem hK (A : PAlg l) (s : Finset ℕ) (w : ℕ → A.W)
    (h : ∑ k ∈ s, A.cris 1 (d (l * k)) * A.toAcr 1 (w k) = 0) (k : ℕ) (hks : k ∈ s) :
    w k ∈ Ideal.span {algebraMap (Ainf l) A.W r0, (l : A.W)} := by
  have hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0 := by
    rw [expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]
  have hk := (GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A _).1 hexp k
  rw [Finsupp.indicator_of_mem hks] at hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hk
  have hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l) := by
    change A.sW _ = _
    rw [r0, sW, WittVector.map_teichmuller, map_pow]
    rfl
  have hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hr]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [hb, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)
  exact Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩

theorem natCast_acr (A : PAlg l) : (l : A.Acr 1) = 0 := by
  have := A.pow_l_acr 1
  rwa [pow_one] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W),
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 →
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  intro l _ A z hz
  exact generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0
    (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1))
    hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz

end Specific

end GlobalTheory.CompanionTheory.TensOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedColumnAverageExists
section
noncomputable section

open MeasureTheory Matrix Filter Topology PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem col_add {F : Type} [Field F] (n k : ℕ) (x y : Fin (k + 1) → F) :
    col n k (x + y) = col n k x * col n k y := by
  apply Units.ext
  show 1 + cM n k (x + y) = (1 + cM n k x) * (1 + cM n k y)
  have h : cM n k (x + y) = cM n k x + cM n k y := by
    ext i j
    simp only [cM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h, mul_add, add_mul, add_mul, cM_mul]
  simp [add_assoc]

theorem exists_weak_integral {X V : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup V] [Module ℂ V] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (Λ : Set X) (hc : IsCompact Λ) (hΛ : MeasurableSet Λ) (φ : X → ℂ) (hφ : Continuous φ)
    (f : X → V) (hf : IsLocallyConstant f) :
    ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ x in Λ, φ x * l (f x) ∂ν := by
  classical
  have hS : (f '' Λ).Finite := by
    haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc
    have h := (hf.comp_continuous (continuous_subtype_val (p := (· ∈ Λ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h
  have hmeas : ∀ v, MeasurableSet (Λ ∩ f ⁻¹' {v}) := fun v =>
    hΛ.inter (hf.isOpen_fiber v).measurableSet
  have hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun x => φ x * l (f x) := fun l =>
    hφ.mul (hf.comp l).continuous
  refine ⟨∑ v ∈ hS.toFinset, (∫ x in Λ ∩ f ⁻¹' {v}, φ x ∂ν) • v, fun l => ?_⟩
  have hU : Λ = ⋃ v ∈ hS.toFinset, Λ ∩ f ⁻¹' {v} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.Finite.mem_toFinset, exists_prop]
    exact ⟨fun hx => ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
  have hdisj : Set.PairwiseDisjoint (↑hS.toFinset) fun v => Λ ∩ f ⁻¹' {v} := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    exact hxa.2.symm.trans hxb.2
  have hint : ∀ s, s ⊆ Λ → ∀ g : X → ℂ, Continuous g → IntegrableOn g s ν := fun s hs g hg =>
    (hg.continuousOn.integrableOn_compact hc).mono_set hs
  conv_rhs => rw [hU]
  rw [integral_biUnion_finset _ (fun v _ => hmeas v) hdisj
    (fun v _ => hint _ Set.inter_subset_left _ (hcont l)), map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, smul_eq_mul, ← integral_mul_const]
  refine setIntegral_congr_fun (hmeas v) fun x hx => ?_
  have hx2 : f x = v := hx.2
  simp only [hx2]

theorem twisted_column_average_exists : L0 → L3 := by
  intro h0
  unfold L3 ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ k M ξ u
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  obtain ⟨hcomp, -, hmeas, -⟩ := (hL (k + 1)).1 M
  have hopen0 : IsOpen (lat F (k + 1) 0) := ((hL (k + 1)).1 0).2.1
  have hϖ : (uniformizer F : F) ≠ 0 := uniformizer_ne_zero F
  obtain ⟨c, hc⟩ := hρ u
  have hfix : ∀ y : Fin (k + 1) → F, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (c + 1) * t) →
      ρ (col n k y) u = u := by
    intro y hy
    apply hc
    intro i j
    show ∃ t ∈ 𝒪[F], ((1 + cM n k y) - 1) i j = (uniformizer F : F) ^ (c + 1) * t
    rw [add_sub_cancel_left]
    simp only [cM, Matrix.of_apply]
    split_ifs with h
    · exact hy _
    · exact ⟨0, zero_mem _, by simp⟩
  have hcol : ∀ x y : Fin (k + 1) → F, ∀ v, ρ (col n k (x + y)) v = ρ (col n k x) (ρ (col n k y) v) := by
    intro x y v
    rw [col_add, map_mul]
    rfl
  have hf : IsLocallyConstant fun x : Fin (k + 1) → F => ρ (col n k x) u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hcont : Continuous fun y : Fin (k + 1) → F =>
        ((uniformizer F : F) ^ (c + 1))⁻¹ • (y - x) := by fun_prop
    have h0mem : ((uniformizer F : F) ^ (c + 1))⁻¹ • (x - x) ∈ lat F (k + 1) 0 := by
      intro i
      simp
    have hev := hcont.continuousAt.eventually_mem (hopen0.mem_nhds h0mem)
    filter_upwards [hev] with y hy
    have hy' : ρ (col n k (y - x)) u = u := by
      refine hfix _ fun i => ⟨((uniformizer F : F) ^ (c + 1))⁻¹ * (y - x) i, ?_, ?_⟩
      · simpa using hy i
      · field_simp
    show ρ (col n k y) u = ρ (col n k x) u
    rw [show ρ (col n k y) u = ρ (col n k (x + (y - x))) u by rw [add_sub_cancel], hcol, hy']
  have hdot : Continuous fun x : Fin (k + 1) → F => ξ ⬝ᵥ x := by
    simp only [dotProduct]
    fun_prop
  have hφ : Continuous fun x : Fin (k + 1) → F => ψ (-(ξ ⬝ᵥ x)) := hψc.comp hdot.neg
  obtain ⟨w, hw⟩ := exists_weak_integral (Measure.pi fun _ : Fin (k + 1) => μ) (lat F (k + 1) M)
    hcomp hmeas _ hφ _ hf
  refine ⟨w, hw, fun y hy => ?_⟩
  have hpre : (fun x => y + x) ⁻¹' lat F (k + 1) M = lat F (k + 1) M := by
    ext x
    constructor
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := sub_mem h1 h2
      simpa [mul_add] using h3
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := add_mem h2 h1
      simpa [mul_add] using h3
  refine sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun l => ?_)
  have hl := hw (l ∘ₗ ρ (col n k y))
  have htr := (measurePreserving_add_left (Measure.pi fun _ : Fin (k + 1) => μ) y).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft y).measurableEmbedding
    (fun x => ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n k x) u)) (lat F (k + 1) M)
  rw [hpre] at htr
  have hψy : ∀ x, ψ (-(ξ ⬝ᵥ x)) = ψ (ξ ⬝ᵥ y) * ψ (-(ξ ⬝ᵥ (y + x))) := by
    intro x
    rw [← AddChar.map_add_eq_mul, dotProduct_add]
    congr 1
    ring
  have hmain : l (ρ (col n k y) w) = ψ (ξ ⬝ᵥ y) * l w := by
    have e1 : l (ρ (col n k y) w) = (l ∘ₗ ρ (col n k y)) w := rfl
    rw [e1, hl, hw l, ← htr, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [LinearMap.comp_apply]
    rw [hcol, hψy x, mul_assoc]
  rw [map_sub, map_smul, smul_eq_mul, hmain, sub_self]

end GlobalTheory.CompanionTheory.SatakeBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFinite
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
end

