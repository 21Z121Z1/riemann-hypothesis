import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjectDefiniteLieEigenLatticeDegreeDifference
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff0

theorem idxZero {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L N : Submodule (𝓞 K) V) : idx K 0 L N = ⊤ := by
  have : detSpan K 0 N = detSpan K 0 L := by
    unfold detSpan
    congr 1
    ext w
    simp
  rw [idx, this]
  exact (Ideal.eq_top_iff_one _).2 (Submodule.mem_colon.2 fun _ h => by simpa using h)

theorem cmDiff_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re := by

  intro E _ _ _ H hH _ χ hχ K _ _ ρ σ₁ p q X F h hF hq τ hτ
  subst hq
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A b).pol).some
  have hM : ∀ j : Fin p ⊕ Fin 0, ∃ M, (FA j.isLeft).IsDiffOf F (X.φ j) M := fun j =>
    (DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ F (X.φ j) (X.lin j).1).1.exists
  choose M hM using hM
  obtain ⟨gP, gQ, hg⟩ := GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject E H K ρ σ₁ p 0 X
  have hD : IsDiffs (FA true) (FA false) F (fun a => M (.inl a)) (fun a => M (.inr a)) :=
    ⟨fun a => hM (.inl a), fun a => hM (.inr a)⟩
  obtain ⟨𝔫, h𝔫₀, hid₀⟩ := GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal E H hH K ρ σ₁ p X gP gQ hg
  have hQd : gQ.det = 1 := Matrix.det_fin_zero
  have h𝔫 : 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} := by
    rw [hQd, mul_one]; exact h𝔫₀
  have hid' : idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ) * Ideal.span {τ gQ.det} =
      𝔫.map τ * idx K 0 (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ (FA false) F (fun a => M (.inr a)) (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
    rw [hQd, map_one, Ideal.span_singleton_one, Ideal.mul_top, idxZero, Ideal.mul_top]
    exact hid₀ (FA true) F (fun a => M (.inl a)) hD.1 τ hτ
  obtain ⟨hP0, hQ0, hdP, hdQ⟩ :=
    GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H K ρ σ₁ p 0 X χ hχ gP gQ hg (FA true) (FA false) F _ _ hD h hF τ hτ
  obtain ⟨hle, hrk1, -, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA F M hM
  set τb : 𝓞 E →+* 𝓞 K := τ.comp (H.bar : 𝓞 E →+* 𝓞 E) with hτb
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτb' : τb H.rt = -ρ := by
    simp [hτb, GlobalTheory.CM.EigDec.bar_rt, hτ]
  have hne : ¬ τb H.rt = ρ := by
    rw [hτb']
    intro e
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact hρ ((mul_eq_zero.1 this).resolve_left two_ne_zero)
  have hdec := (GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ X.B F p 0 X.split X.typeB X.ρ_sq).1
  have hrkP : latRank K (F.eigLat X.B.t.act τ) = p := by rw [hdec, if_pos hτ]
  have hrkQ : latRank K (F.eigLat X.B.t.act τb) = 0 := by rw [hdec, if_neg hne]
  have hfg : ∀ σ, (F.eigLat X.B.t.act σ).FG := fun σ =>
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ F).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hsubP : subP (FA true) F (fun a => M (.inl a)) τ ≤ F.eigLat X.B.t.act τ :=
    iSup_le fun a => hle (.inl a, τ)
  have hsubQ : subQ (FA false) F (fun a => M (.inr a)) τb ≤ F.eigLat X.B.t.act τb :=
    iSup_le fun a => hle (.inr a, τb)
  have hrsP : latRank K (subP (FA true) F (fun a => M (.inl a)) τ) = p := by
    unfold subP
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin p => ((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ))
      fun a b e => by simpa using e)).trans ?_
    have h1 : ∀ a : Fin p, latRank K (((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K))) = 1 := fun a => by
      have := hrk1 (.inl a, τ)
      simpa [hτ] using this
    calc _ = ∑ _a : Fin p, 1 := Finset.sum_congr rfl fun a _ => h1 a
      _ = p := by simp
  have hrsQ : latRank K (subQ (FA false) F (fun a => M (.inr a)) τb) = 0 := by
    unfold subQ
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin 0 => ((FA false).eigLat (X.A false).t.act τb).map
        ((M (.inr a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin 0 => ((Sum.inr a : Fin p ⊕ Fin 0), τb))
      fun a b e => by simpa using e)).trans ?_
    simp
  obtain ⟨hneP, hdegP⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h p _ _ hsubP (hfg τ) hrkP hrsP
  obtain ⟨hneQ, hdegQ⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h 0 _ _ hsubQ (hfg τb) hrkQ hrsQ
  rw [hdegP, hdegQ, hdP, hdQ]
  have hdvd := (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ ⊥).1
  have hfE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfK : 0 < Module.finrank ℚ K := Module.finrank_pos
  set n := Module.finrank ℚ K / Module.finrank ℚ E with hn
  have hnK : (Module.finrank ℚ K : ℝ) = n * Module.finrank ℚ E := by
    rw [hn, Nat.cast_div hdvd (by exact_mod_cast hfE.ne')]
    field_simp
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hfK hdvd) hfE
  have hbar : Ideal.absNorm (𝔫.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔫 := by
    rw [(GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E E _ 𝔫).2, Nat.div_self hfE, pow_one]
  have hnorm : ∀ x : 𝓞 E, (Ideal.absNorm (Ideal.span {x}) : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := fun x => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  have hspan : Ideal.span {τ gQ.det} = (Ideal.span {gQ.det}).map τ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at hid'
  have e1 := congrArg Ideal.absNorm hid'
  rw [map_mul, map_mul, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2] at e1
  have e2 := congrArg Ideal.absNorm h𝔫
  rw [map_mul, hbar, ← Ideal.span_singleton_mul_span_singleton, map_mul] at e2
  have hA : (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneP)
  have hB : (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneQ)
  have hP1 : (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hP0))
  have hQ1 : (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hQ0))
  have hN1 : (Ideal.absNorm 𝔫 : ℝ) ≠ 0 := by
    intro h0
    have : ((Ideal.absNorm 𝔫 * Ideal.absNorm 𝔫 : ℕ) : ℝ) = 0 := by push_cast; rw [h0, zero_mul]
    rw [e2] at this
    push_cast at this
    exact (mul_ne_zero hP1 hQ1) this
  have l1 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e1
  have l2 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e2
  simp only [Nat.cast_mul, Nat.cast_pow] at l1 l2
  rw [Real.log_mul hA (pow_ne_zero _ hQ1), Real.log_mul (pow_ne_zero _ hN1) hB, Real.log_pow, Real.log_pow] at l1
  rw [Real.log_mul hN1 hN1, Real.log_mul hP1 hQ1] at l2
  rw [← hnorm, ← hnorm]
  have hfE' : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast hfE.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have key : Real.log (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ)
        / Module.finrank ℚ K
      - Real.log (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ)
        / Module.finrank ℚ K =
      Real.log (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) / (2 * Module.finrank ℚ E)
        - Real.log (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) / (2 * Module.finrank ℚ E) := by
    rw [← sub_div, ← sub_div, hnK]
    rw [div_eq_div_iff (mul_ne_zero hn' hfE') (mul_ne_zero two_ne_zero hfE')]
    linear_combination (2 * Module.finrank ℚ E : ℝ) * l1 + (n : ℝ) * (Module.finrank ℚ E : ℝ) * l2
  linear_combination key

end GlobalTheory.FlatCore.CMDiff0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSpaceIntegers
section
set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.UPel.HT

namespace GlobalTheory.AdelicLimitCompactness

theorem exists_limit_compact (p : ℕ) (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : O, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : O, a = (c n : O) + n * b := by
  let I := {n : ℕ // 0 < n ∧ Nat.Coprime n p}
  haveI : Nonempty I := ⟨⟨1, one_pos, Nat.coprime_one_left p⟩⟩
  let S : I → Set O := fun n => Set.range fun b : O => (c n.1 : O) + (n.1 : O) * b
  have hcomp : ∀ n, IsCompact (S n) := fun n => isCompact_range (by fun_prop)
  have hsub : ∀ (n k : I) (m : ℕ), 0 < m → k.1 = n.1 * m → S k ⊆ S n := by
    rintro n k m hm hk _ ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := hc n.1 m n.2.1 hm (hk ▸ k.2.2)
    refine ⟨z + m * b, ?_⟩
    simp only [hk, hz]
    push_cast
    ring
  have hdir : Directed (fun x y => x ⊇ y) S := by
    intro n m
    refine ⟨⟨n.1 * m.1, Nat.mul_pos n.2.1 m.2.1, Nat.Coprime.mul_left n.2.2 m.2.2⟩, ?_, ?_⟩
    · exact hsub n _ m.1 m.2.1 rfl
    · exact hsub m _ n.1 n.2.1 (mul_comm _ _)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir
    (fun n => Set.range_nonempty _) hcomp (fun n => (hcomp n).isClosed)
  refine ⟨a, fun n hn hp => ?_⟩
  obtain ⟨b, hb⟩ := Set.mem_iInter.1 ha ⟨n, hn, hp⟩
  exact ⟨b, hb.symm⟩

theorem compactSpace_integers {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

variable {p : ℕ}

def ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : AfP p :=
  RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)

theorem eval_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) (v : AwayP p) :
    AfP.eval v (ofInt x) = x v := rfl

theorem isInt_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : IsIntAf (ofInt x) :=
  fun v => (x v).2

theorem afp_ext {a b : AfP p} (h : ∀ v, AfP.eval v a = AfP.eval v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem exists_limit_adele (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : AfP p, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : AfP p, IsIntAf b ∧ a = (c n : AfP p) + n * b := by
  have h : ∀ v : AwayP p, ∃ a : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → Nat.Coprime n p →
      ∃ b : v.1.adicCompletionIntegers ℚ, a = (c n : v.1.adicCompletionIntegers ℚ) + n * b := fun v =>
    haveI := compactSpace_integers v.1
    exists_limit_compact p _ c hc
  choose a ha using h
  refine ⟨ofInt a, fun n hn hp => ?_⟩
  choose b hb using fun v => ha v n hn hp
  refine ⟨ofInt b, isInt_ofInt b, afp_ext fun v => ?_⟩
  rw [map_add, map_mul, map_intCast, map_natCast, eval_ofInt, eval_ofInt, hb v]
  push_cast
  rfl

variable [Fact p.Prime] (D : Datum p)

def inHom : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem smul_inAf (a : AfP p) (x : D.La) : a • inAf D x = a ⊗ₜ ((1 : ℚ) ⊗ₜ x) := by
  rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem smul_inAf_mem {a : AfP p} (ha : IsIntAf a) (x : D.La) : a • inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨a, x, ha, smul_inAf D a x⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    rw [← smul_inAf, smul_smul]
    exact smul_inAf_mem D (fun v => by rw [map_mul]; exact mul_mem (ha v) (ha' v)) x
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_adelic_limit (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) :
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  have hB : ∀ i, B i = inAf D (b i) := fun i => by
    simp only [B, Algebra.TensorProduct.basis_apply, inAf]
  have hlim := fun i j => exists_limit_adele (p := p) (fun n => b.repr (g n (b i)) j) (by
    intro n m hn hm hp
    obtain ⟨z, hz⟩ := hg n m hn hm hp (b i)
    exact ⟨b.repr z j, by simp [hz]⟩)
  choose a ha using hlim
  let h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := B.constr (AfP p) fun i => ∑ j, a i j • inAf D (b j)
  have h₀b : ∀ i, h₀ (inAf D (b i)) = ∑ j, a i j • inAf D (b j) := fun i => by
    rw [← hB]; exact B.constr_basis _ _ i
  have key : ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La,
      ∃ w ∈ LaHat D, h₀ (inHom D x) = inHom D (g n x) + n • w := by
    intro n hn hp x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      choose e he he' using fun j => ha i j n hn hp
      refine ⟨∑ j, e j • inAf D (b j), sum_mem fun j _ => smul_inAf_mem D (he j) _, ?_⟩
      conv_rhs => rw [← b.sum_repr (g n (b i)), map_sum]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (h₀b i).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [he' j, map_zsmul, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul]
      rfl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, e⟩ := hx
      obtain ⟨w', hw', e'⟩ := hy
      refine ⟨w + w', add_mem hw hw', ?_⟩
      rw [map_add, map_add, e, e', map_add, map_add, nsmul_add]
      abel
    | smul k x _ hx =>
      obtain ⟨w, hw, e⟩ := hx
      refine ⟨k • w, zsmul_mem hw k, ?_⟩
      rw [map_zsmul, map_zsmul, e, map_zsmul, map_zsmul, zsmul_add, smul_comm k n w]
  refine ⟨h₀, fun v hv => ?_, key⟩
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := key 1 one_pos (Nat.coprime_one_left p) x
    rw [← smul_inAf, map_smul]
    change a' • h₀ (inHom D x) ∈ _
    rw [e, smul_add, one_nsmul]
    exact add_mem (smul_inAf_mem D ha' _) (smul_mem D ha' hw)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (D : Datum p) (g : ℕ → D.La →+ D.La),
    (∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) →
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w :=
  fun _ _ D g hg => exists_adelic_limit D g hg

end GlobalTheory.AdelicLimitCompactness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeOneDifferCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem compatibleForms_cocycles_differ_by_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H1.mk _ (m.coef.pullbackOneCocycle f) = H1.mk _ f' := h.symm
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h'
  have hinj := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.1.injective
  have hz : (morMap m).p1 k.1 - k'.1 ∈ (KK κ' t').Z1 :=
    sub_mem ((morMap m).z1 k).2 k'.2
  have h0 : (KK κ' t').fnMap.h1 (QuotientAddGroup.mk ⟨_, hz⟩ : (KK κ' t').H1) = 0 := by
    change (QuotientAddGroup.mk ((KK κ' t').fnMap.z1 ⟨_, hz⟩) : Cx.H1 _) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ
      have e := congrFun (congrFun (congrFun hg T) T') φ
      have e1 := congrFun (congrFun (congrFun hk (m.obj T)) (m.obj T')) (m.functor.map φ)
      have e2 := congrFun (congrFun (congrFun hk' T) T') φ
      refine e.trans ?_
      exact congrArg₂ (fun u v : T'.B ↦ u - v) e1.symm e2.symm
    · funext T
      rfl
  have h1 := hinj (h0.trans (map_zero (KK κ' t').fnMap.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeTwoDifferCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.ClsTwo

universe u

theorem cob_of_fn_cob {C : Type u} [Category.{0} C] (K : Cx C) (h : Function.Injective K.fnMap.h2)
    (z : K.T2) (hz : z ∈ K.Z2) (e : K.M0.c1)
    (he : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (e T T' φ) - e T T'' (φ ≫ ψ) + e T' T'' ψ = z.1 T T' T'' φ ψ) :
    ∃ g, K.D1 g = z := by
  have h0 : K.fnMap.h2 (QuotientAddGroup.mk ⟨z, hz⟩) = 0 := by
    change (QuotientAddGroup.mk (K.fnMap.z2 ⟨z, hz⟩) : (Cx.single K.M0).H2) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(e, 0), ?_⟩
    refine Prod.ext ?_ rfl
    funext T T' T'' φ ψ
    exact he T T' T'' φ ψ
  have h1 : (QuotientAddGroup.mk ⟨z, hz⟩ : K.H2) = 0 := h (h0.trans (map_zero _).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem cob_of_class_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H2.mk _ (m.coef.pullbackTwoCocycle f) = H2.mk _ f' := h.symm
  obtain ⟨e, he⟩ := H2.mk_eq_mk.1 h'
  refine cob_of_fn_cob (KK κ' t') (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.2.injective _
    (AddSubgroup.sub_mem _ ((morMap m).p2_mem_Z2_of_mem_Z2 k.2) k'.2) e ?_
  intro T T' T'' φ ψ
  have h1 := congrFun (congrFun (congrFun (congrFun (congrFun he T) T') T'') φ) ψ
  refine h1.trans ?_
  have h2 : (m.coef.pullbackTwoCocycle f).1 T T' T'' φ ψ = ((morMap m).p2 k.1).1 T T' T'' φ ψ :=
    (congrFun (congrFun (congrFun (congrFun (congrFun hk _) _) _) (m.functor.map φ)) (m.functor.map ψ)).symm
  have h3 := congrFun (congrFun (congrFun (congrFun (congrFun hk' T) T') T'') φ) ψ
  exact congrArg₂ (fun a b : (O κ' t').obj T'' ↦ a - b) h2 h3.symm

end GlobalTheory.PDForm.ClsTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarking
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_exp_unique : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) P (y : Sp ℂ ⟶ F.X) e e', 3 ≤ N → FullMark N D' t → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D' t P y e' → e = e' := by
  intro O _ bar g ρ R _ σ Λ F N D' t P y e e' hN hfull hu hu'
  obtain ⟨w, h, ⟨hiso, hmark⟩, hPw, he⟩ :=
    GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ R σ Λ F N D' D' t t P P y e e' (by omega) hu hu'
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hu.2.1
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add, map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  have hid : hR = LinearMap.id := LinearMap.ext_on_range hspan fun a => by
    show h (P a) = P a
    rw [← hPw, ← hσ, key]
    rfl
  funext z
  have hz : h z = z := LinearMap.congr_fun hid z
  rw [← he z, hz]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar | exact GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar | (intros; apply GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJetsStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformed_lattice_sum_derivatives_eq_eisenstein_jets : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  first | exact @GlobalTheory.HilbFam.iterD_defSum_eq_jet | exact GlobalTheory.HilbFam.iterD_defSum_eq_jet | (intros; apply GlobalTheory.HilbFam.iterD_defSum_eq_jet <;> assumption)
end

