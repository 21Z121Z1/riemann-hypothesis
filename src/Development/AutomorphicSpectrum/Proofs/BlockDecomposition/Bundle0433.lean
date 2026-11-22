import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0198
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0088
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjective
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem mk_mem_fixed_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd) := by
  intro k _ _ _ _ N h d hd J _ hc _ _ V _ _ π _ v x
  have hx : leviEmb k (stdBlocks d hd) (x : Levi k (Bl d)) ∈ J := x.2
  have hv : π (leviEmb k (stdBlocks d hd) (x : Levi k (Bl d))) (v : V) = (v : V) := by
    simpa using v.2 ⟨_, hx⟩
  have hδ : deltaHalf k (Bl d) (x : Levi k (Bl d)) = 1 := GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hc x x.2
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevel
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.JacSmooth

theorem jac_fixed_of_smooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd,
        jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  intro k _ _ _ _ n hd V _ _ π hπ w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨m, hm, hK⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k n {g | π g v = v} (hπ v) (by simp)
  refine ⟨m, hm, fun u hu => ?_⟩
  have hδ : deltaHalf k (PositivityTheory.Lbc.Bl (fun _ : Fin n => 1)) u = 1 :=
    GlobalTheory.T.modulus_trivial_on_levi_compact k n n (fun _ : Fin n => 1) hd (Zls.Km k n m) (GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km n m) u hu
  have hv : π (leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) u) v = v := hK hu
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.JacSmooth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorLiftDominant
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassPush

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_mul (π : Representation ℂ G V) (a b : G) (v : V) : π a (π b v) = π (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

theorem mem_fixed_iff (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have h1 : ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v := hv
    simpa using h1 ⟨h, hh⟩
  · intro hv
    show ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v
    intro h
    simpa using hv h h.2

theorem mkQ_avg (W : Submodule ℂ V) (r : ℕ) (hr : 0 < r) (f : Fin r → V) (m : V ⧸ W)
    (h : ∀ i, W.mkQ (f i) = m) : W.mkQ (((r : ℂ)⁻¹) • ∑ i, f i) = m := by
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  rw [map_smul, map_sum, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr', one_smul]

end SlopeTestRemainingChoices

section Avg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_avg (K : Subgroup G) (hK : IsCompact (K : Set G)) (π : Representation ℂ G V)
    (hπ : IsSmooth π) (E : V →ₗ[ℂ] V)
    (hE : ∀ (u : V) (H : Subgroup G), H ≤ K → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G),
      0 < r → (∀ i, x i ∈ K) → (∀ y ∈ K, ∃! i, (x i)⁻¹ * y ∈ H) →
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u)
    (u : V) (A : Subgroup G) (hA : A ≤ K) (hc : ∀ y ∈ K, ∃ a ∈ A, π (a⁻¹ * y) u = u) :
    ∃ (r : ℕ) (x : Fin r → G), 0 < r ∧ (∀ i, x i ∈ A) ∧
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let H' : Subgroup K :=
    { carrier := {g | π (g : G) u = u}
      mul_mem' := by
        intro a b ha hb
        show π ((a * b : K) : G) u = u
        rw [Subgroup.coe_mul, ← pi_mul, show π (b : G) u = u from hb, show π (a : G) u = u from ha]
      one_mem' := by
        show π ((1 : K) : G) u = u
        simp
      inv_mem' := by
        intro a ha
        show π ((a⁻¹ : K) : G) u = u
        have ha' : π (a : G) u = u := ha
        conv_lhs => rw [← ha']
        rw [pi_mul]
        simp }
  have hH' : IsOpen (H' : Set K) := (hπ u).preimage continuous_subtype_val
  have hcomp : IsCompact (((⊤ : Subgroup K)) : Set K) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set K))
  obtain ⟨r, hr, x, hxA, hx⟩ := GlobalTheory.T.compact_group_finite_coset_reps K ⊤ H' (A.subgroupOf K) hcomp hH' le_top le_top (by
    intro y _
    obtain ⟨a, ha, hau⟩ := hc y y.2
    refine ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, ?_⟩
    show π (((⟨a, hA ha⟩ : K)⁻¹ * y : K) : G) u = u
    simpa using hau)
  refine ⟨r, fun i => (x i : G), hr, fun i => Subgroup.mem_subgroupOf.1 (hxA i),
    hE u (H'.map K.subtype) ?_ ?_ r _ hr (fun i => (x i).2) ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact hg
  · intro y hy
    obtain ⟨i, hi, huniq⟩ := hx ⟨y, hy⟩ trivial
    refine ⟨i, ⟨(x i)⁻¹ * ⟨y, hy⟩, hi, by simp⟩, ?_⟩
    rintro i' ⟨g, hg, e⟩
    refine huniq i' ?_
    have : (x i')⁻¹ * ⟨y, hy⟩ = g := by
      apply Subtype.ext
      simpa using e.symm
    show (x i')⁻¹ * ⟨y, hy⟩ ∈ H'
    rw [this]
    exact hg

end Avg

section Dom

variable {G : Type} [Group G] [TopologicalSpace G]

theorem conj_pow_mem (D : CassData G) (t : D.T) (hd : D.IsDom t) (j : ℕ) :
    ∀ b ∈ D.J ⊓ D.T, ((t : G) ^ j)⁻¹ * b * (t : G) ^ j ∈ D.J ⊓ D.T := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    have h := (hd.2.2 _ (ih b hb)).2
    have e : ((t : G) ^ (j + 1))⁻¹ * b * (t : G) ^ (j + 1)
        = (t : G)⁻¹ * (((t : G) ^ j)⁻¹ * b * (t : G) ^ j) * (t : G) := by
      rw [pow_succ]; group
    rw [e]
    exact h

end Dom

theorem exists_fixed_proj_eq_piN_pow : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  intro G _ _ _ D V _ _ π hπ t ht w hw
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨hd, -, hsh⟩ := ht
  obtain ⟨j, hj⟩ := hsh {g | π g u = u} (hπ u) (by simp)
  have hwT := (mem_fixed_iff _ _ _).1 hw
  have hKc : IsCompact ((D.J ⊓ D.T : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hN : ∀ n ∈ D.N, ∀ v : V,
      (twKer π D.N 1).mkQ (π n v) = (twKer π D.N 1).mkQ v := by
    intro n hn v
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨n, hn⟩, v, by simp⟩)

  obtain ⟨x, hxdef⟩ : ∃ x, x = π ((t : G) ^ j) u := ⟨_, rfl⟩
  have hxNm : ∀ n ∈ D.J ⊓ D.Nm, π n x = x := by
    intro n hn
    have h1 : π (((t : G) ^ j)⁻¹ * n * (t : G) ^ j) u = u := hj n hn
    rw [hxdef]
    conv_rhs => rw [← h1]
    rw [pi_mul, pi_mul]
    congr 2
    group

  obtain ⟨E1, hE1fix, -, -, -, hE1⟩ := GlobalTheory.T.compact_fixed_vector_projection G (D.J ⊓ D.T) hKc V π hπ
  obtain ⟨r, b, hr, hb, hy⟩ := exists_avg (D.J ⊓ D.T) hKc π hπ E1 hE1 x (D.J ⊓ D.T) le_rfl
    (fun y hy => ⟨y, hy, by simp⟩)
  obtain ⟨y, hydef⟩ : ∃ y, y = E1 x := ⟨_, rfl⟩
  rw [← hydef] at hy
  have hyK : ∀ k ∈ D.J ⊓ D.T, π k y = y := by
    rw [hydef]
    exact (mem_fixed_iff _ _ _).1 (hE1fix x)
  have hyNm : ∀ n ∈ D.J ⊓ D.Nm, π n y = y := by
    intro n hn
    rw [hy, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi := hb i
    have hn' : (b i)⁻¹ * n * b i ∈ D.J ⊓ D.Nm := by
      refine ⟨D.J.mul_mem (D.J.mul_mem (inv_mem hbi.1) hn.1) hbi.1, ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (D.norm_Nm _ (inv_mem hbi.2)) n).1 hn.2
      simpa using h2
    have h3 := hxNm _ hn'
    conv_rhs => rw [← h3]
    rw [pi_mul, pi_mul]
    congr 2
    group
  have hmk : (twKer π D.N 1).mkQ y = D.piN π (t ^ j) (Submodule.Quotient.mk u) := by
    rw [hy]
    refine mkQ_avg _ r hr _ _ fun i => ?_
    have hc := conj_pow_mem D t hd j (b i) (hb i)
    have hfix := hwT ⟨_, hc.2⟩ hc.1
    have h4 : π (b i) x = π ((t : G) ^ j) (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u) := by
      rw [hxdef, pi_mul, pi_mul]
      congr 2
      group
    rw [h4]
    have h5 : (twKer π D.N 1).mkQ (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u)
        = Submodule.Quotient.mk u := hfix
    have h6 : ∀ m : V, (twKer π D.N 1).mkQ (π ((t : G) ^ j) m)
        = D.piN π (t ^ j) ((twKer π D.N 1).mkQ m) := by
      intro m
      have : (((t ^ j : D.T)) : G) = (t : G) ^ j := by simp
      rw [← this]
      rfl
    rw [h6, h5]

  obtain ⟨E2, hE2fix, -, -, -, hE2⟩ := GlobalTheory.T.compact_fixed_vector_projection G D.J D.isCompact_J V π hπ
  obtain ⟨r2, c, hr2, hc, hv⟩ := exists_avg D.J D.isCompact_J π hπ E2 hE2 y (D.J ⊓ D.N) inf_le_left
    (fun g hg => by
      obtain ⟨c, hc, b', hb', a, ha, rfl⟩ := D.fact_up g hg
      refine ⟨c, hc, ?_⟩
      have e : c⁻¹ * (c * b' * a) = b' * a := by group
      rw [e, ← pi_mul, hyNm a ha, hyK b' hb'])
  refine ⟨j, ⟨E2 y, hE2fix y⟩, ?_⟩
  show (twKer π D.N 1).mkQ (E2 y) = _
  rw [hv]
  refine mkQ_avg _ r2 hr2 _ _ fun i => ?_
  rw [hN _ (hc i).2, hmk]

end GlobalTheory.CompanionTheory.CassPush
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRightStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_right : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_l | exact GlobalTheory.CompanionTheory.KunGlue.glue_l | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_l <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormula
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCupInv

attribute [local instance 2000] Rep.hV2

theorem pow_identity {F : Type} [Field F] {n m p q r s : ℕ} {ζ y : F} (hy : y ≠ 0) (hζ : ζ ^ n = 1)
    (h : s + q = n * m + r) :
    (ζ ^ p * y) ^ q / y ^ r * y ^ s = ζ ^ ((p * q) % n) * (y ^ n) ^ m := by
  have e : y ^ s * y ^ q = (y ^ n) ^ m * y ^ r := by
    rw [← pow_add, ← pow_mul, ← pow_add, h]
  rw [mul_pow, ← pow_mul, ← pow_eq_pow_mod _ hζ]
  have hr : y ^ r ≠ 0 := pow_ne_zero _ hy
  field_simp
  linear_combination (ζ ^ (p * q)) * e

theorem kummer_key {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n m p q r s k : ℕ} (ζ y u : Ωˣ)
    (g : Ω ≃ₐ[K] Ω) (hζ : ζ ^ n = 1) (hu : (u : Ω) = (y : Ω) ^ n)
    (hg : g (y : Ω) = (ζ : Ω) ^ p * y) (hk : k = (p * q) % n) (h : s + q = n * m + r) :
    (Additive.ofMul (ζ ^ k) + (m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (y ^ q)) - Additive.ofMul (y ^ r) +
        Additive.ofMul (y ^ s) := by
  apply Additive.toMul.injective
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply, map_pow, hg]
  rw [hu, pow_identity y.ne_zero (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]) h, hk]

theorem unramifiedDegree_liftNormal_localArtinMap {K Ω : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]
    {a : Kˣ} (ha : ord (a : K) = 1) :
    unramifiedDegree K Ω ((localArtinMap K Ω a).liftNormal Ω) = Multiplicative.ofAdd 1 := by
  rw [← restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff]
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes ((localArtinMap K Ω a).liftNormal Ω)
    (maximalUnramifiedExtension K Ω) y
  have h2 := AlgEquiv.liftNormal_commutes (localArtinMap K Ω a) Ω
    ⟨(y : Ω), maximalUnramifiedExtension_le_maximalAbelianExtension y.2⟩
  have h3 := localArtinMap_uniformizer_apply (Ω := Ω) ha y.2
  simp only [IntermediateField.algebraMap_apply] at h1 h2
  rw [h1, h2]
  exact h3

theorem inv_kummerCup : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  intro K Ω _ _ _ _ _ _ _ _ _ _ _ n _ ζ y a hζ hord hy κ χ hκ hadd hcont hdeg x hx
  have hlc : IsLocallyConstant χ := (IsLocallyConstant.iff_continuous χ).2 hcont
  let ψ : Additive Gal(Ω/K) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ n (χ (Additive.toMul σ))
      map_zero' := by
        have h1 : χ 1 = 0 := by simpa using hadd 1 1
        simp [h1]
      map_add' := fun σ τ => by simp [hadd]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ n)).continuous }
  let z : cocycles (galUnitsZ K Ω) 2 := cocyclesULiftInt (galUnits.{0} K Ω) x
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω a)
  let f : Gal(Ω/K) → galUnitsZ K Ω := fun g => Additive.ofMul (y ^ (χ g).val)
  have hf : IsLocallyConstant f := hlc.comp fun c : ZMod n => (Additive.ofMul (y ^ c.val) : galUnitsZ K Ω)
  have hz : cohomologyπ (galUnitsZ K Ω) 2 (z + w) = 0 := by
    refine (cohomologyπ_two_eq_zero_iff _ _).2 ⟨f, hf, fun g h => ?_⟩
    have ez : cochainOf (galUnitsZ K Ω) (cocycleι _ 2 z) ![g, h] =
        Additive.ofMul (ζ ^ (κ g * χ h).val) :=
      (congrFun (cochainOf_cocycleι_cocyclesULiftInt (galUnits.{0} K Ω) x) ![g, h]).trans (hx _)
    set m : ℕ := ((χ g).val + (χ h).val) / n with hm
    have em : charCocycle (charAdd ψ) ((![g, h] : Fin 2 → Gal(Ω/K)) 0, (![g, h] : Fin 2 → Gal(Ω/K)) 1) =
        (m : ℤ) :=
      charCocycle_eq_bockInt χ (charAdd ψ) (fun _ => rfl) g h
    have hsum : (χ g).val + (χ h).val = n * m + (χ (g * h)).val := by
      rw [hadd, ZMod.val_add]
      exact (Nat.div_add_mod _ _).symm
    let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) a
    have key := kummer_key ζ y u g hζ (show (u : Ω) = (y : Ω) ^ n from hy.symm) (hκ g)
      (show (κ g * χ h).val = ((κ g).val * (χ h).val) % n from ZMod.val_mul _ _) hsum
    rw [map_add, cochainOf_add, Pi.add_apply, ez, hwc, em]
    exact key
  have e1 : cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2 (cohomologyπ _ 2 x) =
      cohomologyπ (galUnitsZ K Ω) 2 z :=
    cohomologyULiftIntAddEquiv_cohomologyπ' _ x
  have e2 : brauerInv K Ω (cohomologyπ _ 2 x) = brauerInvZ K Ω (cohomologyπ (galUnitsZ K Ω) 2 z) := by
    rw [← e1, brauerInvZ_cohomologyULiftIntAddEquiv]
  have e3 : cohomologyπ (galUnitsZ K Ω) 2 z + galCupClass K Ω ψ a = 0 := by
    rw [galCupClass, ← hw, ← map_add]
    exact hz
  have e4 := brauerInvZ_galCupClass_liftNormal ψ a
  have e5 : ψ (Additive.ofMul ((localArtinMap K Ω a).liftNormal Ω)) = zmodToQZ n 1 := by
    change zmodToQZ n (χ ((localArtinMap K Ω a).liftNormal Ω)) = _
    rw [hdeg _ (unramifiedDegree_liftNormal_localArtinMap hord)]
  have e6 := congrArg (brauerInvZ K Ω) e3
  rw [map_add, map_zero, e4, e5] at e6
  rw [e2]
  exact eq_neg_of_add_eq_zero_left e6

end GlobalTheory.CompanionTheory.KummerCupInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorphStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_homeomorph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  first | exact @GlobalTheory.CompanionTheory.LeviIso.leviEquiv | exact GlobalTheory.CompanionTheory.LeviIso.leviEquiv | (intros; apply GlobalTheory.CompanionTheory.LeviIso.leviEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitNodeEmbeddingStatement
section
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_node_embedding : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  first | exact @GlobalTheory.CompanionTheory.TreeNode.nodeEmb | exact GlobalTheory.CompanionTheory.TreeNode.nodeEmb | (intros; apply GlobalTheory.CompanionTheory.TreeNode.nodeEmb <;> assumption)
end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtensionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_finite_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | exact GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | (intros; apply GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariant_cup_kummer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  first | exact @GlobalTheory.CompanionTheory.KapChi.cup_class_eq | exact GlobalTheory.CompanionTheory.KapChi.cup_class_eq | (intros; apply GlobalTheory.CompanionTheory.KapChi.cup_class_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCountStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_local_zero_count : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.crofton_chart | exact GlobalTheory.CompanionTheory.FSCrofton.crofton_chart | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.crofton_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.GPMem

theorem mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  have hlast : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
      (Fin.last (m + j)) = GlobalTheory.BZMir.eLast k (m + j) :=
    (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (m + j + 1)) k)).1 g.2
  have hproj : ∀ a b : Fin (m + j),
      ((GlobalTheory.BZMir.mirabolicProjection k (m + j) g : GL (Fin (m + j)) k) : Matrix (Fin (m + j)) (Fin (m + j)) k) a b =
        ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
  simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
    Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
  constructor
  · intro h b a
    convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
      simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      have h0 : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.last (m + j))
          (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : m + j = m + j) (Sum.inl a))) = 0 := by
        rw [hlast]
        simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
        rw [if_neg (Fin.castSucc_lt_last _).ne]
      convert h0 using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    | cast b =>
      convert h b a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]

end GlobalTheory.CompanionTheory.GPMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [GlobalTheory.T.mirabolic_character_eq k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (GlobalTheory.T.mirabolic_filtration_exhaustive k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
end

