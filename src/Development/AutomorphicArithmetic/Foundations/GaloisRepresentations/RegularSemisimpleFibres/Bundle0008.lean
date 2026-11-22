import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnrOfIne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unrOfIne :
    UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI
  have hunder : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    ext x
    show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal
    rw [← hw, ← hv]
    have hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K) := by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      rfl
    rw [hx]
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩
  have hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap M Ω).injective
    show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hI t ht x
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← (UpperTheory.V.CF.ineCard).1 K M w, hinert]
    simp
  refine ⟨hunder, ?_, ?_⟩
  · rintro ⟨w', hw'⟩
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]
    exact he
  · intro x hx hmem
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    have hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
      exact he
    have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal :=
      Ideal.map_le_iff_le_comap.2 hcomap.ge
    have hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2 :=
      fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1
    by_cases hxv : x ∈ v.asIdeal
    · obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x} :=
        Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)
      have hJv : ¬ J ≤ v.asIdeal := by
        intro h
        apply hx
        rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
        exact Ideal.mul_mono_right h
      have hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal := by
        intro h
        rw [Ideal.map_le_iff_le_comap, hcomap] at h
        exact hJv h
      have hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤ := by
        by_contra hne
        exact hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))
      have hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤ := by
        have hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal :=
          Ideal.isCoprime_iff_sup_eq.2 hsup
        exact Ideal.isCoprime_iff_sup_eq.1 hc.pow_right
      apply hnot
      have hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
        exact hmem
      have hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2 :=
        Ideal.mul_le_right
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal
          = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal *
              (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2) := by rw [hsup2, Ideal.mul_top]
        _ = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ⊔
              Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 := by
            rw [Ideal.mul_sup, hJ, Ideal.map_mul]
        _ ≤ w.asIdeal ^ 2 := sup_le hx2 hr
    · apply hxv
      rw [← hcomap, Ideal.mem_comap]
      exact Ideal.pow_le_self two_ne_zero hmem
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SumFstMap
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons' {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b n : ℕ) (h : (Y.map Sigma.fst).sum = b) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h; rfl

private theorem sum_fst_map {F : Type} [Field F] (f : ℕ × ℕ → (Σ m : ℕ, GL (Fin m) F → ℂ))
    (hf : ∀ p, (f p).1 = p.1) (L : List (ℕ × ℕ)) :
    ((L.map f).map Sigma.fst).sum = deg L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih, hf]
    rfl

private theorem J_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) :
    ∀ n, J θ L n = hcL (L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction L with
  | nil => intro n; rfl
  | cons p L ih =>
    intro n
    rw [J_cons, List.map_cons, hcL_cons' _ _ (deg L) n (sum_fst_map _ (fun _ => rfl) L), ih]

private theorem JD_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) :
    ∀ n, JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction D with
  | nil => intro n; simpa [JD_nil] using J_eq θ L n
  | cons p D ih =>
    intro n
    have hs : (((D.map (fun p : ℕ × ℕ => (⟨p.1, detc θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))) ++
        L.map (fun p : ℕ × ℕ => (⟨p.1, cusp θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).map Sigma.fst).sum =
        deg D + deg L := by
      rw [List.map_append, List.sum_append, sum_fst_map _ (fun _ => rfl) D, sum_fst_map _ (fun _ => rfl) L]
    rw [JD_cons, List.map_cons, List.cons_append, hcL_cons' _ _ (deg D + deg L) n hs, ih]

private theorem cusp_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    cusp θ 1 k = detc θ 1 k := by
  haveI : Fintype F := Fintype.ofFinite F
  funext x
  have hcp : Matrix.charpoly (x : Matrix (Fin 1) (Fin 1) F) = X - C ((x : Matrix (Fin 1) (Fin 1) F) 0 0) := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin 1 → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
    (Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F))
    (by rw [Matrix.charpoly_toLin', hcp]; exact irreducible_X_sub_C _)
  rw [Matrix.charpoly_toLin', hcp] at hval
  simp only [cusp, psiG, detc, Nat.sub_self, pow_zero, one_mul]
  rw [hval, Matrix.det_fin_one]
  simp [GlobalTheory.CuspGL.rootSum]

theorem UpperTheory.Gal.InertialTypesAlt.jdEq :
    JDEq := by
  intro F _ _ θ
  refine ⟨fun D L n => JD_eq θ D L n, cusp_one θ, ?_⟩
  intro D L n
  cases D with
  | nil =>
    cases L with
    | nil => intro x y; rfl
    | cons p L => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
  | cons p D => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
end

