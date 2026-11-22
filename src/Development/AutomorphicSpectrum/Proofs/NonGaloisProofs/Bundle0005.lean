import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0004
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0074

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.FinCoc

section Generic

variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (by simp [actT])

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem pow_nsmul_quot (L : Lattice (O := O) ρ) {ϖ : O} {n : ℕ} (hn : (n : O) ∈ Ideal.span {ϖ}) (r : ℕ)
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) : n ^ r • m = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hn
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r := by
    rw [Nat.cast_pow, ← hu, mul_pow, mul_comm]
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [TopologicalSpace V] [ContinuousAdd V]

theorem mk_isLocallyConstant (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    IsLocallyConstant (fun x : ↥L.T =>
      (Submodule.Quotient.mk x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : ↥L.T => (y : V) + -(x : V) :=
    continuous_subtype_val.add continuous_const
  have hev := hc.continuousAt.eventually_mem (x := x)
    (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)
  filter_upwards [hev] with y hy
  obtain ⟨t, ht, h⟩ := hy
  rw [Submodule.Quotient.eq]
  have hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T) :=
    Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)
  rw [hxy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_quot (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ} (hC : IsCompact (L.T : Set V))
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    Finite (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) := by
  have hcs : CompactSpace ↥L.T := isCompact_iff_compactSpace.1 hC
  refine Set.finite_univ_iff.1 ?_
  rw [← (Submodule.Quotient.mk_surjective _).range_eq]
  exact (mk_isLocallyConstant L hW).range_finite

theorem actQ_isLocallyConstant [TopologicalSpace G] (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V))
    (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hc : Continuous fun g : G => actT L g t := (hcont (t : V)).subtype_mk _
  exact (mk_isLocallyConstant L hW).comp_continuous hc

end Generic

theorem finZQ_of_duality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), FinZQ ((D.loc l).PD K) := by
  intro hT hE D l _ K LL _ _ _ O _ _ hg A LA ϖ hϖ r hI
  obtain ⟨-, -, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hg ϖ hϖ
  obtain ⟨-, hB, hC, -, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hg A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have hMfin := finite_quot LA hC hW
  have hfin := GlobalTheory.CocycleCount.cocycles_finite_ncard_le hT hE l K r _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI)
    (fun g h m => actQ_mul' LA _ hI g h m) (pow_nsmul_quot LA hl r)
    (actQ_isLocallyConstant LA hW A.cont hI)
  exact hfin.1.to_subtype

end GlobalTheory.CompanionTheory.FinCoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsFinsetSep
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add, hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add, map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

theorem right_kernel (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (hD : DualD ((D.loc l).PD K)) (hC : CobLO ((D.loc l).PD K))
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hP : IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P)
    (b : ↥(GK K) → A'.V) (hb : b ∈ continuousCocycles A'.ρ)
    (hab : ∀ a ∈ continuousCocycles A.ρ, CobL ((D.loc l).PD K) (cupL A'.ρ P a b)) : b ∈ B1 A'.ρ := by
  classical
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := id hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨LA, LA', hLat, -⟩ := (GlobalTheory.T.exists_dual_lattices D l K).2 LL O hO A A' P hP
  obtain ⟨-, hLat2⟩ := id hLat
  obtain ⟨L1, hL1⟩ := (GlobalTheory.T.exists_dual_lattices D l K).1 LL O hO
  have h52 := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A' LA' ϖ hϖ
  have h53 := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  have hb' : Continuous b ∧ ∀ g h, b (g * h) = b g + A'.ρ g (b h) := hb
  obtain ⟨β, hβdef⟩ : ∃ β : LL, β = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hβ : β ≠ 0 := by
    rw [hβdef]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective O LL (h.trans (map_zero _).symm))
  have hmkLC : IsLocallyConstant (Submodule.Quotient.mk (p := LA'.T)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(· + -x) ⁻¹' (LA'.T : Set A'.V),
      h52.1.preimage (continuous_add_const _), ?_, fun x' hx' => ?_⟩
    · simp
    · exact (Submodule.Quotient.eq _).2 (by simpa [sub_eq_add_neg] using hx')
  have hactD : ∀ g (v : A'.V), Formalism.WeaklyAdmissibleFiltrations.actD LA' g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A'.ρ g v) :=
    fun g v => rfl
  have hlift : ∀ q : A'.V ⧸ LA'.T, Submodule.Quotient.mk (Formalism.MainNotions.N.liftD LA' q) = q := fun q => by
    unfold Formalism.MainNotions.N.liftD
    generalize_proofs hq
    exact hq.choose_spec
  have e1 : ∀ (v : A'.V) g, (LinearMap.pi fun g => Formalism.WeaklyAdmissibleFiltrations.actD LA' g - LinearMap.id)
      (Submodule.Quotient.mk v : A'.V ⧸ LA'.T) g = Submodule.Quotient.mk (A'.ρ g v - v) := fun v g => by
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hactD, Submodule.Quotient.mk_sub]
  have hBZ : BD LA' ≤ divisibleCocycles LA' := by
    intro s hs
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hs
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    show IsLocallyConstant _ ∧ ∀ g h, _ = _ + Formalism.WeaklyAdmissibleFiltrations.actD LA' g _
    refine ⟨?_, fun g h => ?_⟩
    · have hf : (fun g => (LinearMap.pi fun g => Formalism.WeaklyAdmissibleFiltrations.actD LA' g - LinearMap.id)
          (Submodule.Quotient.mk v : A'.V ⧸ LA'.T) g) =
          (Submodule.Quotient.mk (p := LA'.T)) ∘ fun g => A'.ρ g v + -v := funext fun g => by
        rw [e1, sub_eq_add_neg]; rfl
      have hcont : Continuous fun g : ↥(GK K) => A'.ρ g v + -v := (A'.cont v).add continuous_const
      have hlc := hmkLC.comp_continuous hcont
      convert hlc using 1
    · rw [e1, e1, e1, hactD, ← Submodule.Quotient.mk_add]
      congr 1
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
  have step : ∀ n : ℕ, ∃ x : A'.V, ∀ g, (β ^ n)⁻¹ • b g - (A'.ρ g x - x) ∈ LA'.T := by
    intro n
    have hc : (fun g => (Submodule.Quotient.mk ((β ^ n)⁻¹ • b g) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
      show IsLocallyConstant _ ∧ ∀ g h, _ = _ + Formalism.WeaklyAdmissibleFiltrations.actD LA' g _
      refine ⟨hmkLC.comp_continuous (hb'.1.const_smul _), fun g h => ?_⟩
      simp only
      rw [hactD, ← Submodule.Quotient.mk_add, hb'.2 g h, smul_add, map_smul]
    have hcS := hD LL O hO L1 hL1 A A' LA LA' P hLat (BD LA') le_rfl hBZ _ hc (by
      intro d hd _
      have hd1 : d ∈ continuousCocycles A.ρ := (Submodule.mem_inf.1 hd).1
      have hdT : ∀ g, d g ∈ LA.T := fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hd).2) g (Set.mem_univ g)
      have hcup := (hC LL O hO L1 hL1 _ (h53.2 d hd1 b hb).1).1 (hab d hd1) ((β ^ n)⁻¹)
      unfold Formalism.MainNotions.N.CobO at hcup ⊢
      convert hcup using 2
      rename_i x
      rw [Submodule.Quotient.eq, hL1]
      have hl := (Submodule.Quotient.eq LA'.T).1 (hlift (Submodule.Quotient.mk ((β ^ n)⁻¹ • b x.2)))
      obtain ⟨a, ha⟩ := (hLat2 _).1 (LA'.stable x.1 _ hl) (d x.1) (hdT x.1)
      refine ⟨a, ?_⟩
      rw [Algebra.linearMap_apply, ← ha]
      simp only [Formalism.MainNotions.N.cupLD, Formalism.MainNotions.N.cupL, Pi.smul_apply, smul_eq_mul, map_sub, map_smul])
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hcS
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x, fun g => ?_⟩
    have h1 := congr_fun hz g
    rw [e1] at h1
    have h2 := LA'.T.neg_mem ((Submodule.Quotient.eq LA'.T).1 h1)
    rwa [neg_sub] at h2
  obtain ⟨U, hU⟩ : ∃ U : Submodule LL (↥(GK K) → A'.V), U = Submodule.span LL {b} ⊔ B1 A'.ρ := ⟨_, rfl⟩
  haveI hB1fd : FiniteDimensional LL ↥(B1 A'.ρ) := LinearMap.finiteDimensional_range _
  haveI : FiniteDimensional LL ↥U := by
    rw [hU]
    exact Submodule.finiteDimensional_sup _ _
  obtain ⟨F, hF⟩ := exists_finset_sep (k := LL) U.subtype
  let Φ : A'.V →ₗ[O] (↥F → A'.V) := (LinearMap.pi fun f : ↥F => A'.ρ f - LinearMap.id).restrictScalars O
  let Λ : Submodule O (↥F → A'.V) := ⨆ f : ↥F, LA'.T.map (LinearMap.single O (fun _ : ↥F => A'.V) f)
  have hΛ : Λ.FG := Submodule.fg_iSup _ fun f => LA'.fg.map _
  have hw : (fun f : ↥F => b f) ∈ LinearMap.range Φ := by
    refine mem_of_forall_pow Λ (LinearMap.range Φ) hΛ ϖ hϖ.not_isUnit _ fun n => ?_
    obtain ⟨x, hx⟩ := step n
    refine ⟨Φ (β ^ n • x), LinearMap.mem_range_self _ _, fun f => (β ^ n)⁻¹ • b f - (A'.ρ f x - x), ?_, ?_⟩
    · rw [← Finset.univ_sum_single (fun f : ↥F => (β ^ n)⁻¹ • b f - (A'.ρ f x - x))]
      exact Submodule.sum_mem _ fun f _ => Submodule.mem_iSup_of_mem f ⟨_, hx f, rfl⟩
    · funext f
      have e2 : (ϖ ^ n) • ((β ^ n)⁻¹ • b f - (A'.ρ f x - x)) = b f - β ^ n • (A'.ρ f x - x) := by
        rw [← algebraMap_smul LL (ϖ ^ n), map_pow, ← hβdef, smul_sub, smul_inv_smul₀ (pow_ne_zero n hβ)]
      show b f = Φ (β ^ n • x) f + (ϖ ^ n) • ((β ^ n)⁻¹ • b f - (A'.ρ f x - x))
      rw [e2]
      simp only [Φ, LinearMap.restrictScalars_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, smul_sub]
      abel
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hw
  have hu : b - Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ x ∈ U := by
    rw [hU]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self b))
      (Submodule.mem_sup_right (LinearMap.mem_range_self (Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ) x))
  have hzero : b - Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ x = 0 := hF ⟨_, hu⟩ fun g hg => by
    have h1 := congr_fun hx ⟨g, hg⟩
    simp only [Φ, LinearMap.restrictScalars_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h1
    simp only [Submodule.coe_subtype, Pi.sub_apply, Formalism.WeaklyAdmissibleFiltrations.cob, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    rw [h1, sub_self]
  exact LinearMap.mem_range.2 ⟨x, (sub_eq_zero.1 hzero).symm⟩

theorem nondegL : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), DualD ((D.loc l).PD K) →
    CobLO ((D.loc l).PD K) → NondegL ((D.loc l).PD K) := by
  intro D l _ K hD hC
  unfold GlobalTheory.CompanionTheory.LocDual.NondegL
  intro LL _ _ _ O _ _ hO A A' P hP
  have h53 := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  refine ⟨fun a ha hab => ?_, fun b hb hab => right_kernel D l K hD hC LL O hO A A' P hP b hb hab⟩
  exact right_kernel D l K hD hC LL O hO A' A P.flip h53.1 a ha fun b hb => ((h53.2 a ha b hb).2.2.1).1 (hab b hb)

end GlobalTheory.CompanionTheory.LocDual.Kernels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.FinT

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_smulTop (L : Lattice (O := O) ρ) (ϖ : O) (x : ↥L.T) :
    x ∈ (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, ϖ • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem fg_Z1T [TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V] (L : Lattice (O := O) ρ) {ϖ : O}
    (h0 : algebraMap O LL ϖ ≠ 0)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hK : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T)) (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG :=
  _root_.UpperTheory.Reformulated.B.Gub2.fg_Z1T L h0 hB hK hI hfin

theorem t2Space_of_lattice_nhds_basis [IsTopologicalAddGroup V] [IsNoetherianRing O] [IsLocalRing O] (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : ¬ IsUnit ϖ)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V))) :
    T2Space V := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hcon
  push_neg at hcon
  have hin : ∀ n : ℕ, ∃ t ∈ L.T, ϖ ^ n • t = x := fun n => hcon _ (hB.mem_of_mem (i := n) trivial)
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥L.T) (Ideal.span {ϖ})
    (fun h => hϖ (Ideal.span_singleton_eq_top.1 h))
  obtain ⟨t₀, ht₀, he₀⟩ := hin 0
  have hxT : x ∈ L.T := by
    rw [pow_zero, one_smul] at he₀
    exact he₀ ▸ ht₀
  have hmem : (⟨x, hxT⟩ : ↥L.T) ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • (⊤ : Submodule O ↥L.T)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨t, ht, he⟩ := hin n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨t, ht⟩, trivial, Subtype.ext he⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx (congrArg Subtype.val hmem)

def toV (L : Lattice (O := O) ρ) : LatticeCohomology L →ₗ[O] H1V ρ :=
  Submodule.liftQ _
    (((Submodule.mkQ ((B1 ρ).comap (continuousCocycles ρ).subtype)).restrictScalars O) ∘ₗ
      { toFun := fun c => ⟨(c : G → V), c.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (by
      rintro c ⟨x, _, hx⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨x, hx⟩)

theorem toV_mk (L : Lattice (O := O) ρ) (c : ↥(latticeCocycles L)) :
    toV L (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨(c : G → V), c.2.1⟩ := rfl

theorem isLocalized_toV [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) {ϖ : O} (h0 : ϖ ≠ 0)
    (hInt : ∀ c : G → V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ L.T) :
    IsLocalizedModule (nonZeroDivisors O) (toV L) where
  map_units s := by
    have hs : algebraMap O LL (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hxy' : (s : O) • x = (s : O) • y := hxy
      rw [← algebraMap_smul LL (s : O) x, ← algebraMap_smul LL (s : O) y] at hxy'
      exact smul_right_injective _ hs hxy'
    · intro y
      refine ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩
      change (s : O) • ((algebraMap O LL (s : O))⁻¹ • y) = y
      rw [← algebraMap_smul LL (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  surj y := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := hInt (c : G → V) c.2.1
    have hz : ϖ ^ n • (c : G → V) ∈ latticeCocycles L :=
      ⟨(continuousCocycles ρ).restrictScalars O |>.smul_mem _ c.2, fun g _ => hn g⟩
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, ⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩⟩, ?_⟩
    rfl
  exists_of_eq := by
    intro x₁ x₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [toV_mk, toV_mk, Submodule.Quotient.eq] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨n, hn⟩ := hInt (fun _ => v) continuous_const
    refine ⟨⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨ϖ ^ n • v, hn 1, ?_⟩
    funext g
    have hvg : ρ g v - v = (a : G → V) g - (b : G → V) g := congrFun hv g
    change ρ g (ϖ ^ n • v) - ϖ ^ n • v = ϖ ^ n • (a : G → V) g - ϖ ^ n • (b : G → V) g
    rw [← smul_sub, ← hvg, ← algebraMap_smul LL (ϖ ^ n) v, map_smul, ← smul_sub, algebraMap_smul]

end Gen

theorem h1_lattice_finite_rank_eq : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), FinZQ ((D.loc l).PD K) → TateFiniteness ((D.loc l).PD K) ∧ ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank O (LatticeCohomology LA) := by
  intro D l _ K hZ
  have key : ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O)
      (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) := by
    intro LL _ _ _ O _ _ hO A LA
    obtain ⟨⟨hD, hV, hF⟩, -, -, hTR, -⟩ := id hO
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, -, hK, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
    obtain ⟨-, hB, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
    haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
    haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
    haveI : T2Space A.V := t2Space_of_lattice_nhds_basis LA hϖ.not_isUnit hB
    have h0 : algebraMap O LL ϖ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hI : StableSub LA (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥LA.T) := by
      intro g x hx
      obtain ⟨y, rfl⟩ := (mem_smulTop LA ϖ x).1 hx
      exact (mem_smulTop LA ϖ _).2 ⟨actT LA g y, (map_smul _ _ _).symm⟩
    have hfg := fg_Z1T LA h0 hB hK hI (hZ LL O hO A LA ϖ hϖ 1 hI)
    haveI : Module.Finite O ↥(latticeCocycles LA) := Module.Finite.iff_fg.2 hfg
    infer_instance
  refine ⟨key, ?_⟩
  intro LL _ _ _ O _ _ hO A LA
  haveI := key LL O hO A LA
  obtain ⟨⟨hD, hV, hF⟩, -, -, hTR, -⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, -, -, hInt, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
  haveI := isLocalized_toV LA hϖ.ne_zero hInt
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) (toV LA), ?_⟩
  have h1 : Module.rank LL (H1V A.ρ) = Module.rank O (H1V A.ρ) :=
    IsLocalization.rank_eq LL (nonZeroDivisors O) le_rfl
  have h2 : Module.rank O (H1V A.ρ) = Module.rank O (LatticeCohomology LA) :=
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl (toV LA)
  rw [finrank, finrank, h1, h2]

end GlobalTheory.CompanionTheory.LocDual.FinT
end
end

