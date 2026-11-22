import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0071
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open Polynomial in
open scoped Formalism.Per in
private theorem tfab_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tfab_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

theorem UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), g (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → ∀ (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → AI.actT g (y ^ l ^ b) = y ^ l ^ a := by
  intro l hl P AI g a b hg y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := UpperTheory.V.Loc.tfab_lift y hm hy
  have hgx : g (x ^ l ^ b) = x ^ l ^ a := by
    by_cases hx0 : x = 0
    · rw [hx0, zero_pow (pow_ne_zero _ hl.out.ne_zero), zero_pow (pow_ne_zero _ hl.out.ne_zero), map_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := UpperTheory.V.Loc.tfab_root hm hx hx0
    have hmem : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
    have h1 := hg ⟨x, hmem⟩
    rw [GlobalTheory.Pst.frobUr_pow_root b ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn),
      GlobalTheory.Pst.frobUr_pow_root a ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
    exact h1
  have hc : ∀ k : ℕ, PreTilt.coeff 0 (y ^ k) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z ^ k) := fun k => by
    rw [map_pow, h0]
    exact (map_pow _ _ _).symm
  have hz : ∀ k : ℕ, ((z ^ k : OC l) : ℂ_[l]) = ((x ^ k : Om l) : ℂ_[l]) := fun k => by
    rw [PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]
    simp
  have hp : ∀ k : ℕ, (y ^ k) ^ l ^ m = y ^ k := fun k => by rw [← pow_mul, mul_comm, pow_mul, hy]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g (y ^ l ^ b) 0 _ (hc _)
  rw [hz, AI.actC_ext, hgx, ← hz] at h1
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hp]) (hp _) ?_
  rw [h2, hc, Subtype.ext h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfTwistedCommuteOfDistinctCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.linearIndependent_distinct_characters {Γ W ι : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    (ρ : Γ →* Module.End ℂ W) (χ : ι → Γ →* ℂˣ) (y : ι → W) (hy : ∀ i, y i ≠ 0)
    (he : ∀ i σ, ρ σ (y i) = (χ i σ : ℂ) • y i) (hχ : Function.Injective χ) :
    LinearIndependent ℂ y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hinj : Function.Injective (fun i => (Units.coeHom ℂ).comp (χ i)) := by
    intro a b hab
    apply hχ
    ext σ
    exact DFunLike.congr_fun hab σ
  have hli := (linearIndependent_monoidHom Γ ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ φ : Module.Dual ℂ W, c i * φ (y i) = 0 := by
    intro φ
    refine hli (fun j => c j * φ (y j)) ?_ i
    funext σ
    have h1 : φ (ρ σ (∑ j, c j • y j)) = 0 := by rw [hc, map_zero, map_zero]
    rw [map_sum, map_sum] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he, map_smul, map_smul]
    simp only [Pi.smul_apply, Function.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul]
    ring
  by_contra hci
  apply hy i
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  exact (mul_eq_zero.mp (key φ)).resolve_left hci

theorem UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters :
    ∀ {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ) (ν : Γ →* ℂˣ) (N : Module.End ℂ W), Module.finrank ℂ W = n → (∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y) → Function.Injective μ → (∀ j k, μ j ≠ μ k * ν) → (∀ σ, ρ σ * N = (ν σ : ℂ) • (N * ρ σ)) → N = 0 := by
  intro Γ W _ _ _ _ n ρ μ ν N hn hy hμ hlink hN
  choose y hy0 hye using hy
  have hli : LinearIndependent ℂ y := UpperTheory.linearIndependent_distinct_characters ρ μ y hy0 hye hμ
  have hNy : ∀ k, N (y k) = 0 := by
    intro k
    by_contra hk
    have h2 : LinearIndependent ℂ (fun o : Option (Fin n) => o.elim (N (y k)) y) := by
      refine UpperTheory.linearIndependent_distinct_characters ρ (fun o : Option (Fin n) => o.elim (μ k * ν) μ) _ ?_ ?_ ?_
      · rintro (_ | j)
        · exact hk
        · exact hy0 j
      · rintro (_ | j) σ
        · have h3 := LinearMap.congr_fun (hN σ) (y k)
          simp only [Module.End.mul_apply, LinearMap.smul_apply, hye, map_smul, smul_smul] at h3
          simp only [Option.elim_none, MonoidHom.mul_apply, Units.val_mul]
          rw [h3, mul_comm]
        · exact hye j σ
      · rintro (_ | a) (_ | b) hab
        · rfl
        · exact absurd hab.symm (hlink b k)
        · exact absurd hab (hlink a k)
        · exact congrArg some (hμ hab)
    have h4 := h2.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hn] at h4
    omega
  have hspan : Submodule.span ℂ (Set.range y) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])
  refine LinearMap.ext_on_range hspan fun k => ?_
  rw [hNy k, LinearMap.zero_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      (∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W) ∧
      ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n :=
  _root_.UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg ρ hopen M hM hJ

end

theorem UpperTheory.exists_algebraic_vector_spanning_subspace :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M → (∀ g ∈ IK K, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Ainf l), IsUnit W.det ∧ (∀ g, (M g).map (zlW l (OCb l)) * W.map (AI.actW (g : GQ l)) = W) ∧ ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ l ^ m = (W i j).coeff n := by
  intro l _ P AI K r M hM hI
  have := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  exact exists_alg (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (GlobalTheory.UnramifiedCrys.eventually_actT_eq AI y m hm hy)) M hM
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      GlobalTheory.UnramifiedCrys.norm_sub_lt_one_of_fix AI g hg x hx))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenline
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ex_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ q : GL (Fin (n + 1)) k, (q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single 0 1 = v :=
  _root_.UpperTheory.Reformulated.B.ExistsColumnVector.ex_col v hv

theorem UpperTheory.exists_common_eigenline :
    ∀ {H k : Type} [Group H] [TopologicalSpace H] [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + 1)) k) (κ : Fin (n + 1) → H →* kˣ) (v : Fin (n + 1) → k), Continuous r → v ≠ 0 → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v = (κ 0 g : k) • v) → ∃ (p : GL (Fin (n + 1)) k) (r₁ : H →* GL (Fin (n + 1)) k) (r' : H →* GL (Fin n) k), (∀ g, r₁ g = p * r g * p⁻¹) ∧ Continuous r₁ ∧ Continuous r' ∧ (∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0) ∧ (∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k)) ∧ (∀ g (i j : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) k) i j) ∧ (HasFlag r' (fun i => κ i.succ) → HasFlag r κ) :=
  _root_.UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenvectorOfCharpolySplitCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenvector_of_charpoly_split_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (Φ : Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (∀ σ, ∃ (m : ℤ) (s : I), σ = Φ ^ m * i s) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → ∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i Φ ρ μ hnorm hgen hfin hchar j
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ k, (μ k σ : ℂ) := by
    intro σ
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Free.chooseBasis ℂ W),
      Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix, hchar,
      Polynomial.prod_X_sub_C_nextCoeff, neg_neg]
  have heig : ∀ σ k, (ρ σ).HasEigenvalue (μ k σ : ℂ) := by
    intro σ k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  let φ : I →* (Module.End ℂ W)ˣ := (ρ.toHomUnits).comp i
  have hφ : ∀ s, ((φ s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hker : ∀ k, φ.ker ≤ ((μ k).comp i).ker := by
    intro k s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : ρ (i s) = 1 := by rw [← hφ, hs]; rfl
    obtain ⟨v, hv⟩ := (heig (i s) k).exists_hasEigenvector
    have hv1 := hv.apply_eq_smul
    rw [h1, Module.End.one_apply] at hv1
    have h2 : ((μ k (i s) : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, ← hv1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · apply Units.ext
      simp only [MonoidHom.comp_apply, Units.val_one]
      exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have hfinU : (Set.range φ).Finite := by
    refine (Set.Finite.preimage (Function.Injective.injOn (fun a b h => Units.ext h)) hfin).subset ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hr : ∀ q : I ⧸ φ.ker, QuotientGroup.kerLift φ q ∈ Set.range φ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, (QuotientGroup.kerLift_mk φ s).symm⟩
  haveI : Finite (I ⧸ φ.ker) := by
    haveI := hfinU.to_subtype
    exact Finite.of_injective (fun q => (⟨_, hr q⟩ : Set.range φ))
      (fun a b hab => QuotientGroup.kerLift_injective φ (congrArg Subtype.val hab))
  letI : Fintype (I ⧸ φ.ker) := Fintype.ofFinite _
  let R : I ⧸ φ.ker →* Module.End ℂ W := (Units.coeHom (Module.End ℂ W)).comp (QuotientGroup.kerLift φ)
  let c : Fin n → (I ⧸ φ.ker →* ℂˣ) := fun k => QuotientGroup.lift φ.ker ((μ k).comp i) (hker k)
  have hR : ∀ s : I, R (s : I ⧸ φ.ker) = ρ (i s) := fun s => rfl
  have hc : ∀ k (s : I), c k (s : I ⧸ φ.ker) = μ k (i s) := fun k s => rfl
  let E : Submodule ℂ W := ⨅ s, (ρ (i s)).eigenspace (μ j (i s) : ℂ)
  have hmemE : ∀ y, y ∈ E ↔ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y := by
    intro y
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEinv : ∀ y ∈ E, ρ Φ y ∈ E := by
    intro y hy
    rw [hmemE] at hy ⊢
    intro s
    obtain ⟨t, ht⟩ := hnorm Φ⁻¹ s
    have e1 : i s * Φ = Φ * i t := by
      calc i s * Φ = Φ * (Φ⁻¹ * i s) * Φ := by group
        _ = Φ * (i t * Φ⁻¹) * Φ := by rw [ht]
        _ = Φ * i t := by group
    have e2 : μ j (i s) = μ j (i t) := by
      have h3 := congrArg (μ j) e1
      simp only [map_mul] at h3
      rw [mul_comm (μ j Φ)] at h3
      exact mul_right_cancel h3
    calc ρ (i s) (ρ Φ y) = ρ (i s * Φ) y := by rw [map_mul]; rfl
      _ = ρ (Φ * i t) y := by rw [e1]
      _ = ρ Φ (ρ (i t) y) := by rw [map_mul]; rfl
      _ = (μ j (i s) : ℂ) • ρ Φ y := by rw [hy t, map_smul, e2]
  have hmain : ∃ y ∈ E, y ≠ 0 ∧ ρ Φ y = (μ j Φ : ℂ) • y := by
    by_contra hno
    push_neg at hno
    let A : Module.End ℂ E := (ρ Φ).restrict hEinv
    let p := LinearMap.charpoly A
    have hp : p.eval (μ j Φ : ℂ) ≠ 0 := by
      intro h0
      have hA : A.HasEigenvalue (μ j Φ : ℂ) := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr h0
      obtain ⟨v, hv⟩ := hA.exists_hasEigenvector
      have hv0 : (v : W) ≠ 0 := by
        intro h
        apply hv.2
        exact Subtype.ext h
      apply hno v v.2 hv0
      have h5 := congrArg Subtype.val hv.apply_eq_smul
      simpa [A] using h5
    let S := Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) ≠ μ j Φ)
    let h := ∏ k ∈ S, (Polynomial.X - Polynomial.C (μ k Φ : ℂ))
    let f := h * p
    have key : ∀ y (hy : y ∈ E), Polynomial.aeval (ρ Φ) p y = ((Polynomial.aeval A p) ⟨y, hy⟩ : W) := by
      intro y hy
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp [A, Module.End.pow_restrict, LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.End.pow_restrict]
      rfl
    have hfE : ∀ y ∈ E, Polynomial.aeval (ρ Φ) f y = 0 := by
      intro y hy
      rw [Polynomial.aeval_mul, Module.End.mul_apply, key y hy, LinearMap.aeval_self_charpoly]
      simp
    let P : Module.End ℂ W := ∑ q : I ⧸ φ.ker, (((c j q)⁻¹ : ℂˣ) : ℂ) • R q
    have hRP : ∀ a, R a * P = ((c j a : ℂˣ) : ℂ) • P := by
      intro a
      simp only [P, Finset.mul_sum, mul_smul_comm, ← map_mul, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun q => ?_)
      simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
      congr 1
      rw [← Units.val_mul, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    have hPE : ∀ w, P w ∈ E := by
      intro w
      rw [hmemE]
      intro s
      rw [← hR s, ← Module.End.mul_apply, hRP, LinearMap.smul_apply, hc]
    have hfP : Polynomial.aeval (ρ Φ) f * P = 0 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hfE _ (hPE w)
    have htrq : ∀ s : I, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * ρ (i s)) =
        ∑ k, f.eval (μ k Φ : ℂ) * (μ k (i s) : ℂ) := by
      intro s
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, ← map_pow, ← map_mul, htr]
      simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Polynomial.eval_eq_sum_range,
        Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => by ring))
    have hq : ∀ q, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * R q) =
        ∑ k, f.eval (μ k Φ : ℂ) * (c k q : ℂ) := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hR, htrq]
      rfl
    have htot : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) =
        ∑ k, f.eval (μ k Φ : ℂ) * ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) := by
      simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => by ring))
    have hψ : ∀ k, ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) =
        ((if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0 : ℕ) : ℂ) := by
      intro k
      rw [← sum_hom_units]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [div_eq_mul_inv]
    have hzero : ∀ k, (μ k Φ : ℂ) ≠ μ j Φ → f.eval (μ k Φ : ℂ) = 0 := by
      intro k hk
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (i := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) (by simp), zero_mul]
    have hfl : f.eval (μ j Φ : ℂ) ≠ 0 := by
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)) hp
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hk).2)
    let N : ℕ := ∑ k ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ),
      (if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0)
    have hN : N ≠ 0 := by
      have hj : j ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ) := by simp
      have h7 : (Units.coeHom ℂ).comp (c j / c j) = 1 := by simp
      intro h8
      have h9 := (Finset.sum_eq_zero_iff.mp h8) j hj
      rw [if_pos h7] at h9
      exact Fintype.card_ne_zero h9
    have heq : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) = f.eval (μ j Φ : ℂ) * N := by
      rw [htot]
      simp only [hψ, N, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : (μ k Φ : ℂ) = μ j Φ
      · rw [if_pos hk, hk]
      · rw [if_neg hk, hzero k hk, zero_mul]
    rw [hfP, map_zero] at heq
    exact mul_ne_zero hfl (Nat.cast_ne_zero.mpr hN) heq.symm
  obtain ⟨y, hyE, hy0, hyΦ⟩ := hmain
  refine ⟨y, hy0, ?_⟩
  let G : Subgroup Γ :=
    { carrier := {σ | ρ σ y = (μ j σ : ℂ) • y}
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) y = (μ j (a * b) : ℂ) • y
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, Units.val_mul, mul_comm]
      one_mem' := by
        show ρ 1 y = (μ j 1 : ℂ) • y
        simp
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ y = (μ j a⁻¹ : ℂ) • y
        have h4 : y = ρ a⁻¹ (ρ a y) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [ha, map_smul] at h4
        rw [map_inv (μ j), Units.val_inv_eq_inv_val]
        calc ρ a⁻¹ y = (μ j a : ℂ)⁻¹ • ((μ j a : ℂ) • ρ a⁻¹ y) := by
              rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
          _ = (μ j a : ℂ)⁻¹ • y := by rw [← h4] }
  intro σ
  obtain ⟨m, s, rfl⟩ := hgen σ
  have h1 : Φ ∈ G := hyΦ
  have h2 : i s ∈ G := (hmemE y).1 hyE s
  exact G.mul_mem (G.zpow_mem h1 m) h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantOfDpstPhiFixedOfNonnegWeights
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights :
    ∀ {l : ℕ} [Fact l.Prime] {K L : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V), FiniteDimensional ↥L.1 ↥(DdR ((UpperTheory.V.Loc.PP l).PD K) ρ) → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → multV ((UpperTheory.V.Loc.PP l).PD K) ρ τ c = 0) → ∀ z : ↥(Dpst (UpperTheory.V.Loc.PP l) ρ), z ≠ 0 → monD (UpperTheory.V.Loc.PP l) ρ z = 0 → phiD (UpperTheory.V.Loc.PP l) ρ z = z → (∀ g, actD (UpperTheory.V.Loc.PP l) ρ g z = z) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  intro l _ K L key V _ _ _ _ _ ρ hfin hm z hz hN hφ hG
  let P := UpperTheory.V.Loc.PP l
  obtain ⟨y, hy, e⟩ := (mem_Dst_and_monV_eq_zero_iff l P K L V ρ z.1).mp
    ⟨(mem_Dst P ρ).mpr fun g => congrArg Subtype.val (hG g), congrArg Subtype.val hN⟩
  have hy' : ∀ g, actVB (P.PD K) ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).mp hy g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  have c1 : ∀ x : TensorProduct ℚ_[l] V P.R.B, phiV P ↥L.1 V (crisIncl P ↥L.1 V x) =
      crisIncl P ↥L.1 V (LinearMap.lTensor V P.φB.toLinearMap x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have h1 : LinearMap.lTensor V P.φB.toLinearMap y = y := by
    apply crisIncl_injective (LL := ↥L.1) P
    rw [← c1, e]
    exact congrArg Subtype.val hφ
  have c2 : ∀ g (x : TensorProduct ℚ_[l] V P.R.B),
      actVdR (P.PD K) ρ g (LinearMap.lTensor V P.ιB.toLinearMap x) =
      LinearMap.lTensor V P.ιB.toLinearMap (actVB (P.PD K) ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := (P.PD K).ι_comm g b
      rw [P.PD_ι, P.PD_ι] at this
      simp [actVdR, actVB, this]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ DdR (P.PD K) ρ := by
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, c2, hy']
  have h3 := (UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult P key ρ hfin).1 0 hm h2
  have hF : ((P.PD (UpperTheory.V.Loc.botExt l)).Fil 0).restrictScalars ℚ_[l] =
      ((P.PD K).Fil 0).restrictScalars ℚ_[l] := SetLike.coe_injective (P.PD_Fil _ _ 0)
  have h4 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ UpperTheory.V.Loc.FilT ↥L.1 V 0 := by
    unfold UpperTheory.V.Loc.FilT
    unfold FilV at h3
    rw [← hF] at h3
    exact h3
  obtain ⟨v, hv, hu⟩ := UpperTheory.V.Loc.lineInv (A := ↥L.1) y h1 h4
  refine ⟨v, ?_, fun g => hu _ ?_⟩
  · rintro rfl
    apply hz
    apply Subtype.ext
    rw [← e, hv]
    simp
  · have := hy' g
    rw [← this, hv]
    simp [actVB]
end

