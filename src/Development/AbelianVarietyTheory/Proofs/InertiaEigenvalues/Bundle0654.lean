import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMul
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem eS_mul_eS_of_disjoint_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e)
    {I J : Finset ι} (h : Disjoint I J) : eS B e I * eS B e J = 0 := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact he.ortho (fun hij => Finset.disjoint_left.1 h hi (hij ▸ hj))

theorem eS_mul_self_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · exact (he.idem i).eq
  · intro j _ hji; exact he.ortho (Ne.symm hji)
  · intro h; exact absurd hi h

theorem σ_eS_inv [Fintype ι] {e : ι → B.A} {S : Finset ι} (hP : IsPre B e S) (I : Finset ι) :
    B.σ (eS B e I) = eS B e I := by
  unfold eS
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨f, -, -, -, h1, h2⟩ := hP.2 i
  by_cases hi : i ∈ S
  · obtain ⟨h, hf⟩ := h1 hi; rw [h, hf]
  · obtain ⟨-, h⟩ := h2 hi; rw [h, map_add, B.σ_σ, add_comm]

theorem HH_sub_chi_mul_HH_negligible : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι]
    (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A,
    B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  intro K B ι _ _ e π S a hL ha hF I hI x hx
  have hEE := eS_mul_self_inv B hF.1.1 I
  have hE'E := eS_mul_eS_of_disjoint_inv B hF.1.1 (Finset.sdiff_disjoint (s := I) (t := S))
  have hσE := σ_eS_inv B hF.1 I
  have hcov : ∀ i ∈ S, i ∈ I ∨ i ∈ S \ I := fun i hi => by
    by_cases h : i ∈ I
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hi, h⟩)
  set E := eS B e I with hEdef
  set E' := eS B e (S \ I) with hE'def
  obtain ⟨xi, hxi⟩ : ∃ xi : B.A, x * xi = 1 := ⟨_, hx.1.mul_val_inv⟩

  have hyu : IsUnit (x * E + (1 - E)) :=
    IsUnit.of_mul_eq_one (xi * E + (1 - E)) (by linear_combination (E * E) * hxi + (2 - x - xi) * hEE)
  have hx'u : IsUnit (x * (1 - E) + E) :=
    IsUnit.of_mul_eq_one (xi * (1 - E) + E) (by linear_combination (1 - E) ^ 2 * hxi + (2 - x - xi) * hEE)
  have hyP : B.Plus (x * E + (1 - E)) := ⟨hyu, by simp only [map_add, map_mul, map_sub, map_one, hx.2, hσE]⟩
  have hxy : (x * E + (1 - E)) * (x * (1 - E) + E) = x := by linear_combination (-(x - 1) ^ 2) * hEE
  have hchi : chi B e I x = K.eta (Algebra.norm K.E (x * E + (1 - E))) := rfl

  have haU : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a]
    refine (IsUnit.mk0 _ fun h => ha.1 ?_).map _
    exact IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm)

  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hL.2 ha hF
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    (x * (1 - E) + E) (x * E + (1 - E)) hx'u hyu
  obtain ⟨L₁, hL₁⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    1 1 isUnit_one isUnit_one
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Submodule K.O B.A → ℚ, ∀ k M, F k M =
      B.sgnLat M * term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Submodule K.O B.A → ℚ, ∀ k M, G k M =
      B.sgnLat M * term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  have hsg : ∀ M, |B.sgnLat M| = 1 := fun M => by unfold InvAlg.sgnLat; exact abs_eta _
  have hFfin : ∀ k, (B.Lin ∩ Function.support (F k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ ((hx'u.mul (haU.pow _))) hyu).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hFdef, h0, mul_zero])⟩
  have hGfin : ∀ k, (B.Lin ∩ Function.support (G k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ (haU.pow _) isUnit_one).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hGdef, h0, mul_zero])⟩
  have hsub : ∀ k, ∑ᶠ M ∈ B.Lin, (F k M - G k M) = ∑ᶠ M ∈ B.Lin, F k M - ∑ᶠ M ∈ B.Lin, G k M := by
    intro k
    have hFG : (B.Lin ∩ Function.support (fun M => F k M - G k M)).Finite :=
      ((hFfin k).union (hGfin k)).subset fun M ⟨hM, h⟩ => by
        by_cases h1 : F k M = 0
        · exact Or.inr ⟨hM, fun h2 => h (show F k M - G k M = 0 by rw [h1, h2, sub_zero])⟩
        · exact Or.inl ⟨hM, h1⟩
    rw [eq_sub_iff_add_eq, ← finsum_mem_add_distrib' hFG (hGfin k)]
    simp only [sub_add_cancel]

  have key : ∀ k : ℕ, HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 =
      K.eta (Algebra.norm K.E (x * E + (1 - E))) * ∑ᶠ M ∈ B.Lin, (F k M - G k M) := by
    intro k
    have hx_eq : x * algebraMap K.O B.A a ^ (2 * k) =
        (x * E + (1 - E)) * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) := by
      rw [← mul_assoc, hxy]
    rw [hx_eq, GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit K B ι π I (S \ I) _ 1 _ hL hyP, hchi, mul_one, hsub, ← mul_sub]
    congr 1
    unfold HH
    congr 1
    · exact finsum_congr fun M => finsum_congr fun _ => (hFdef k M).symm
    · exact finsum_congr fun M => finsum_congr fun _ => (hGdef k M).symm

  have hcmp := GlobalTheory.T.tendsto_finsum_div_rho_pow_zero K B ι e π S a hL.2 ha hF I (S \ I) hcov N (max L₀ L₁)
    (2 * 2 ^ I.card * 2 ^ (S \ I).card) (fun k M => F k M - G k M) hN
    (by
      intro k M
      rw [hFdef, hGdef, ← mul_sub, abs_mul, hsg, one_mul]
      calc _ ≤ |term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M| +
            |term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M| := abs_sub _ _
        _ ≤ 2 ^ I.card * 2 ^ (S \ I).card + 2 ^ I.card * 2 ^ (S \ I).card :=
            add_le_add (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _)
        _ = _ := by ring)
    (by
      intro k hk M _ p hp hf
      rw [hFdef, hGdef, ← mul_sub] at hf
      have hne := right_ne_zero_of_mul hf
      obtain ⟨h1a, h1b⟩ := hL₀ (max L₀ L₁) (le_max_left _ _) k hk M p hp
      obtain ⟨h2a, h2b⟩ := hL₁ (max L₀ L₁) (le_max_right _ _) k hk M p hp
      rw [one_mul] at h2a h2b
      rw [← hEdef, ← hE'def] at h1b h2b
      have hW : Win I (S \ I) (max L₀ L₁) k p := by
        by_cases h : term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k))
            (x * E + (1 - E)) M = 0
        · exact h2a fun h2 => hne (by rw [h, h2, sub_zero])
        · exact h1a h
      refine ⟨hW, fun hmid => hne ?_⟩
      have hEx : E * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) = E * algebraMap K.O B.A a ^ (2 * k) := by
        linear_combination algebraMap K.O B.A a ^ (2 * k) * (1 - x) * hEE
      have hE'y : E' * (x * E + (1 - E)) = E' * 1 := by linear_combination (x - 1) * hE'E
      rw [h1b hW hmid, h2b hW hmid, hEx, hE'y, sub_self])
  have hfun : (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) = fun k : ℕ =>
      (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ) * (((∑ᶠ M ∈ B.Lin, (F k M - G k M) : ℚ) : ℝ) /
        (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    funext k
    rw [key k, Rat.cast_mul, mul_div_assoc]
  rw [hfun]
  simpa using hcmp.const_mul (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ)

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeTieProof

theorem exists_ext_semilin {L V W U ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (σ : L →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range (fun k => j (b k))) = ⊤)
    (f : V →ₛₗ[σ] U) : ∃ F : W →ₗ[ℂ] U, ∀ v, F (j v) = f v := by
  let bC : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  refine ⟨bC.constr ℂ (fun k => f (b k)), fun v => ?_⟩
  have h : (bC.constr ℂ (fun k => f (b k))).comp j = f := by
    refine b.ext fun k => ?_
    rw [LinearMap.comp_apply]
    have : j (b k) = bC k := by simp [bC]
    rw [this, Module.Basis.constr_basis]
  exact congrArg (fun g : V →ₛₗ[σ] U => g v) h

theorem mem_biSup_of_forall {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (H : ι → Submodule K V)
    (hind : iSupIndep H) (htop : ⨆ x, H x = ⊤) (Y : Set ι) (v : V)
    (h : ∀ x0, x0 ∉ Y → v ∈ ⨆ (x) (_ : x ≠ x0), H x) : v ∈ ⨆ x ∈ Y, H x := by
  classical
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp H v).1 (by rw [htop]; exact Submodule.mem_top)
  have h0 : ∀ x0, x0 ∉ Y → f x0 = 0 := by
    intro x0 hx0
    by_cases hs : x0 ∈ f.support
    · have e : f x0 = v - ∑ x ∈ f.support.erase x0, f x := by
        rw [← hsum, Finsupp.sum, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : f x0 ∈ ⨆ (x) (_ : x ≠ x0), H x := by
        rw [e]
        refine Submodule.sub_mem _ (h x0 hx0) (Submodule.sum_mem _ fun x hx => ?_)
        exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hx) (hf x))
      exact (Submodule.disjoint_def.1 (hind x0)) _ (hf x0) m2
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ Y
  · exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx (hf x))
  · rw [h0 x hx]; exact Submodule.zero_mem _

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_symm {D : D7} {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hxy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hxy, host_conj_eq, host_conj_eq, IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

theorem not_bad_of_splitOut {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w) : s.v ∉ badPl D i := by
  rintro ⟨w', hover, hw'⟩
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq]; simp)).2 h3
  obtain ⟨hsp, hl, hS, hQ⟩ := hw
  rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
  · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e
    · subst e
      exact hQ (HT.Q_conj i s.w w (isConjPl_symm hc) hQ')
    · have ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w := by
        ext1; ext x
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        refine (hc x _ ?_).symm
        rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]
      rw [e, ew] at hQ'
      exact hQ hQ'
  · apply hS
    refine (D.nd.S_def i w).2 ⟨?_, hl⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · exact hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)

theorem tN_lin {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hu : IsUnif D.host.E s.v ϖ) (k : ℕ) (c : ℂ)
    (f f' : GAf D.host.E D.R.nV → (M.loc i).wt.W) :
    tN (M.loc i).J s ϖ k (c • f + f') = c • tN (M.loc i).J s ϖ k f + tN (M.loc i).J s ϖ k f' := by
  have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s ϖ k
    (not_bad_of_splitOut HT i hw s hc) hu
  simp only [tN]
  rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

section Hecke

variable {O X Mo : Type} [CommRing O] [IsDomain O] [AddCommGroup Mo] [Module O Mo]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O Mo)

theorem heckeEig_iSupIndep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) Mo) :=
    fun f => (act f).baseChange (FractionRing O)
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show (act f).baseChange _ * (act g).baseChange _ = (act g).baseChange _ * (act f).baseChange _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).eigenspace_le_genEigenspace (k := 1) (by norm_num)).trans
    (((F f).genEigenspace _).monotone le_top)

theorem dual_eig (htop : ⨆ x, heckeEig T act x = ⊤) (x0 : X)
    (φ : Module.Dual (FractionRing O) (TensorProduct O (FractionRing O) Mo))
    (hφ : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig T act x, φ u = 0) (f : T) (u : TensorProduct O (FractionRing O) Mo) :
    φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u := by
  have hu : u ∈ ⨆ x, heckeEig T act x := by rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction (heckeEig T act)
    (motive := fun u => φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u)
    hu ?_ ?_ ?_
  · intro x u hux
    have he : (act f).baseChange (FractionRing O) u = algebraMap O (FractionRing O) ((f : X → O) x) • u :=
      Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hux f)
    rw [he, map_smul, smul_eq_mul]
    by_cases hx : x = x0
    · rw [hx]
    · rw [hφ x hx u hux, mul_zero, mul_zero]
  · simp
  · intro a b ha hb; rw [map_add, map_add, map_add, ha, hb, mul_add]

end Hecke

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

theorem typeTie_holds : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M →
    SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  intro D M i HT HR AV _ HS HE S y hy
  classical
  let ι : FractionRing (D.nd.O i) →+* ℂ := (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)
  have hι : ∀ a, ι (D.nd.embK i a) = D.what₂.embLL a := D.naut.iota_LL i
  refine mem_biSup_of_forall (heckeEig (D.nd.T i) (D.nd.act i))
    (heckeEig_iSupIndep _ _ (D.nd.T_sep i)) (HE i) {x | ∃ P ∈ S, D.naut.ptV i P = some x} _ ?_
  intro x0 hx0
  by_contra hv
  obtain ⟨φ, hφv, hφB⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ0 : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, φ u = 0 := by
    intro x hx u hu
    have hm : φ u ∈ Submodule.map φ (⨆ (x) (_ : x ≠ x0), heckeEig (D.nd.T i) (D.nd.act i) x) :=
      Submodule.mem_map_of_mem (Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx hu))
    rw [hφB] at hm
    exact (Submodule.mem_bot _).1 hm
  have hφe := dual_eig (D.nd.T i) (D.nd.act i) (HE i) x0 φ hφ0
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  have hb := D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b
  let f0 : D.what₂.MtL (D.nd.mu i) (D.nd.j i) →ₛₗ[D.what₂.embLL] ℂ :=
    { toFun := fun z => ι (φ (D.nd.prMt i z))
      map_add' := fun a c => by simp only [map_add]
      map_smul' := fun a z => by
        show ι (φ (D.nd.prMt i (a • z))) = D.what₂.embLL a • ι (φ (D.nd.prMt i z))
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hι, smul_eq_mul] }
  obtain ⟨Ψ, hΨ⟩ := exists_ext_semilin D.what₂.embLL (D.what₂.jMt _ _) b hb.1 hb.2 f0
  let bC : Module.Basis _ ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ q, bC q = D.what₂.jMt _ _ (b q) := fun q => by simp [bC]
  have hker : ∀ P ∈ S, D.naut.typeV i P ≤ LinearMap.ker Ψ := by
    intro P hP z hz
    by_contra hz0
    rw [LinearMap.mem_ker] at hz0
    apply hx0
    refine ⟨P, hP, (AV.ptV i P x0).2 ?_⟩
    intro w k s ϖ hw hc hu hk1 hk2 y' hy'
    obtain ⟨c, hcP⟩ := HS P w k s ϖ hw hc hu hk1 hk2
    choose x' hx' using HR i w k s ϖ hw hc hu hk1 hk2
    let Tt : Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
      bC.constr ℂ (fun q => D.what₂.jMt _ _ (x' (b q)))
    have hTb : ∀ q, Tt (bC q) = D.what₂.jMt _ _ (x' (b q)) := fun q => by
      simp only [Tt, Module.Basis.constr_basis]
    have t0 : tN (M.loc i).J s ϖ k (0 : GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
      have e := tN_lin HT i hw s hc ϖ hu k 1 0 0
      simp only [smul_zero, add_zero, one_smul] at e
      simpa using e
    let tl : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) :=
      { toFun := tN (M.loc i).J s ϖ k
        map_add' := fun f f' => by simpa using tN_lin HT i hw s hc ϖ hu k 1 f f'
        map_smul' := fun a f => by simpa [t0] using tN_lin HT i hw s hc ϖ hu k a f 0 }
    have hreal : (M.loc i).real ∘ₗ Tt = tl ∘ₗ (M.loc i).real := bC.ext fun q => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hTb, hbC]
      exact hx' (b q)
    have hΨT : Ψ ∘ₗ Tt = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) • Ψ :=
      bC.ext fun q => by
        rw [LinearMap.comp_apply, hTb, LinearMap.smul_apply, hbC, hΨ, hΨ]
        show ι (φ (D.nd.prMt i (x' (b q)))) = _ • ι (φ (D.nd.prMt i (b q)))
        rw [HT.hT i w k s ϖ hw hc hu hk1 hk2 (b q) (x' (b q)) (hx' (b q)), hφe, map_mul, smul_eq_mul]
    have hTz : Tt z = c • z := (M.loc i).real_inj (by
      have e := LinearMap.congr_fun hreal z
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
      rw [e, map_smul]
      exact hcP z hz)
    have hcz : c = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) := by
      have e := LinearMap.congr_fun hΨT z
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hTz, map_smul, smul_eq_mul, smul_eq_mul] at e
      exact mul_right_cancel₀ hz0 e
    rw [hcP y' hy', hcz]
    rfl
  have hyk := (iSup₂_le hker) hy
  rw [LinearMap.mem_ker, hΨ] at hyk
  exact hφv ((map_eq_zero_iff ι ι.injective).1 hyk)

end GlobalTheory.EtaJoin.TypeTieProof
end
end

