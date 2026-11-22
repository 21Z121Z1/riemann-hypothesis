import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FderivEqOfJetOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem isHolFam_precomp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => e (A v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

def colPr (n g : ℕ) (i : Fin n) : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))

theorem colPr_apply (n g : ℕ) (i : Fin n) (v : Fin (n * g) → ℂ) (j : Fin g) :
    colPr n g i v j = v (finProdFinEquiv (i, j)) := rfl

theorem anLin_colPr (n g : ℕ) (i : Fin n) (p : Fin 1 × Fin g) :
    anLin (colPr n g i) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv (i, p.2))]
  · rw [colPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [colPr_apply, Ne.symm hk]
  · simp

theorem renN_colPr (n g m : ℕ) (i : Fin n) (a : Jet ℂ (Fin 1 × Fin g) m) :
    renN n g m (jetMap (anLin (colPr n g i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold renN jetCopy
  exact anJetMap_comp _ _ _ _ _ _
    (fun p => by simp only [anLin_colPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem jetCopy_one_zero (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem spMap_jetCopy_jetPt {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem

theorem AnFr.jetMap_copy (n m : ℕ) (i : Fin n) :
    Φ.JetMap m (homAt x0 (jetCopy (S := ℂ) g m i) ≫ anJX x0 Φ.e Φ.hol m).left (LinearMap.proj i) :=
  ⟨isHolFam_precomp_clm _ Φ.hol (colPr n g i), spMap_jetCopy_jetPt _ Φ.hol n m i⟩

theorem AnFr.jetMap_self (m : ℕ) :
    Φ.JetMap (n := 1) m (anJX x0 Φ.e Φ.hol m).left (LinearMap.proj 0) := by
  refine ⟨isHolFam_precomp_clm _ Φ.hol (colPr 1 g 0), ?_⟩
  have h := spMap_jetCopy_jetPt _ Φ.hol 1 m 0
  have hid : (jetCopy (S := ℂ) g m (0 : Fin 1) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      RingHom.id _ := RingHom.ext (jetCopy_one_zero g m)
  rw [hid, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
  exact h

theorem AnFr.jetMap_one (n m : ℕ) :
    Φ.JetMap m (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A).left 0 := by
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left =
      (1 : Over.mk x0 ⟶ A).left := fun v => by rw [LinearMap.zero_apply, Φ.e_zero]
  have hf := funext hc
  have hol : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left) := by
    rw [hf]; exact isHolFam_const _
  refine ⟨hol, ?_⟩
  have h1 := jetPt_comp _ (isHolFam_const (g := n * g) (1 : Over.mk x0 ⟶ A).left) (𝟙 _) _ hol
    (fun v => (Category.comp_id _).trans (hc v).symm) m
  rw [← h1, Category.comp_id, ← jetPt_const, ← Category.assoc, spMap_comp_alg]
  let k : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ Over.mk x0 :=
    Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin n × Fin g) m))) rfl
  have hk : (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A) = k ≫ (1 : Over.mk x0 ⟶ A) := (MonObj.comp_one k).symm
  rw [hk]
  rfl

theorem AnFr.jetMap_comp {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]

theorem AnFr.jetMap_pair {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]

theorem AnFr.jetMap_mul {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    Φ.JetMap m (a * b).left (Λ + Λ') := by
  obtain ⟨hq, hab⟩ := Φ.jetMap_pair a b Λ Λ' ha hb
  have hc : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (MonObj.mul : A ⊗ A ⟶ A).left = (Φ.e ((Λ + Λ') (colsOf n g v))).left := fun v => by
    rw [LinearMap.add_apply, Φ.e_add, CategoryTheory.Hom.mul_def, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((Λ + Λ') (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hq _
  refine ⟨hol', ?_⟩
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, hab, Category.assoc, jetPt_comp _ hq _ _ hol' hc]

end General

theorem jetPts_jetMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ n m
  exact ⟨fun i => Φ.toAnFr.jetMap_copy n m i, Φ.toAnFr.jetMap_one n m,
    fun a b Λ Λ' ha hb => ⟨Φ.toAnFr.jetMap_mul a b Λ Λ' ha hb, Φ.toAnFr.jetMap_pair a b Λ Λ' ha hb⟩,
    fun a Λ α ha => Φ.toAnFr.jetMap_comp a Λ _ _ (Φ.lin α) ha, Φ.toAnFr.jetMap_self m⟩

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.JetCorr

theorem jet_point_eq {K : Type} [Field K] {J : Type} {m : ℕ} (p : PrimeSpectrum (Jet K J m)) :
    p = IsLocalRing.closedPoint (Jet K J m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn := jet_nilpotent_of_orig K J m (sub_const_mem_orig (R := K) q)
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      refine (IsLocalRing.mem_maximalIdeal _).mp ha ?_
      have e : algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) =
          Ideal.Quotient.mk (orig K J ^ (m + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [← MvPolynomial.algebraMap_eq]; rfl
      have hsplit : Ideal.Quotient.mk (orig K J ^ (m + 1)) q =
          algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) +
            Ideal.Quotient.mk (orig K J ^ (m + 1)) (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [map_sub, e, add_sub_cancel]
      rw [hsplit]
      exact IsNilpotent.isUnit_add_left_of_commute hn
        ((isUnit_iff_ne_zero.mpr hne).map (algebraMap K (Jet K J m))) (Commute.all _ _)
    rwa [h0, map_zero, sub_zero] at hn
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

section JetOf

variable {N : ℕ} (m : ℕ)

theorem jetOf_one' : jetOf m (fun _ : Fin N → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow' {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    jetOf m (fun v => F v ^ k) = jetOf m F ^ k := by
  induction k with
  | zero => simpa using jetOf_one' m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hF.fun_pow k).contDiffAt hF.contDiffAt]
    congr 1

theorem jetOf_mul_inv {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    jetOf m F * jetOf m (fun v => (F v)⁻¹) = 1 := by
  rw [← jetOf_mul m hF.contDiffAt (hF.fun_inv h0).contDiffAt, ← jetOf_one' m]
  refine jetOf_congr m ((hF.continuousAt.eventually_ne h0).mono fun v hv => ?_)
  exact mul_inv_cancel₀ hv

theorem jetOf_zpow {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin N) m)ˣ) (hu : u.val = jetOf m F) (a : ℤ) :
    jetOf m (fun v => F v ^ a) = (u ^ a).val := by
  obtain ⟨k, rfl | rfl⟩ := a.eq_nat_or_neg
  · simp only [zpow_natCast, Units.val_pow_eq_pow_val, hu]
    exact jetOf_pow' m hF k
  · simp only [zpow_neg, zpow_natCast]
    symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow' m hF k]
    exact jetOf_mul_inv m (hF.fun_pow k) (pow_ne_zero _ h0)

theorem jetOf_prod {K : Type} (s : Finset K) {F : K → (Fin N → ℂ) → ℂ} (hF : ∀ k, AnalyticAt ℂ (F k) 0) :
    jetOf m (fun v => ∏ k ∈ s, F k v) = ∏ k ∈ s, jetOf m (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one' m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hF a).contDiffAt
      (Finset.analyticAt_fun_prod s fun k _ => hF k).contDiffAt]
    congr 1
    funext v
    simp [Finset.prod_insert ha]

end JetOf

theorem jetN_prod_zpow {n g : ℕ} (m : ℕ) {K : Type} [Fintype K] (f : K → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, AnalyticAt ℂ (f k) 0) (h0 : ∀ k, f k 0 ≠ 0)
    (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ) :
    ∃ u : K → (Jet ℂ (Fin n × Fin g) m)ˣ, (∀ k, (u k).val = jetN m fun w => f k (Λ k w)) ∧
      jetN m (fun w => ∏ k, f k (Λ k w) ^ ε k) = (∏ k, u k ^ ε k).val := by
  have hc : colsOf n g 0 = 0 := rfl
  have hA : ∀ k, AnalyticAt ℂ (fun v => f k (Λ k (colsOf n g v))) 0 := fun k => by
    have h1 : AnalyticAt ℂ (colsOf n g) 0 :=
      AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))).analyticAt 0
    have h2 : AnalyticAt ℂ (fun v => Λ k (colsOf n g v)) 0 :=
      ((LinearMap.toContinuousLinearMap (Λ k)).analyticAt _).comp h1
    exact (hf k).comp_of_eq h2 (by rw [hc, map_zero])
  have hz : ∀ k, f k (Λ k (colsOf n g 0)) ≠ 0 := fun k => by rw [hc, map_zero]; exact h0 k
  let u0 : K → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k =>
    Units.mkOfMulEqOne _ _ (jetOf_mul_inv m (hA k) (hz k))
  refine ⟨fun k => Units.map (renN n g m).toMonoidHom (u0 k), fun k => rfl, ?_⟩
  unfold jetN
  rw [jetOf_prod m Finset.univ (F := fun k v => f k (Λ k (colsOf n g v)) ^ ε k)
    fun k => (hA k).fun_zpow (hz k), map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [jetOf_zpow m (hA k) (hz k) (u0 k) rfl, ← map_zpow]
  rfl

open scoped Classical in
theorem prod_zpow_fiber {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have h : ∀ ψ, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) = ∏ k, if φ k = ψ then w ψ ^ ε k else 1 := fun ψ => by
    have hz : ∀ t : Finset K, ∀ a : K → ℤ, w ψ ^ (∑ k ∈ t, a k) = ∏ k ∈ t, w ψ ^ a k := fun t a => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]
    rw [hz]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

open scoped Classical in

theorem prod_zpow_eq {M T K K' : Type*} [CommGroup M] [Fintype K] [Fintype K'] (φ : K → T) (ε : K → ℤ)
    (φ' : K' → T) (ε' : K' → ℤ) (u : K → M) (u' : K' → M)
    (h₁ : ∀ k l, φ k = φ l → u k = u l) (h₂ : ∀ k l, φ' k = φ' l → u' k = u' l)
    (h₃ : ∀ k l, φ k = φ' l → u k = u' l)
    (hs : ∀ ψ, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0) :
    ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
  let w : T → M := fun ψ => if h : ∃ k, φ k = ψ then u h.choose else if h' : ∃ k, φ' k = ψ then u' h'.choose else 1
  have hw : ∀ k, u k = w (φ k) := fun k => by
    have h : ∃ l, φ l = φ k := ⟨k, rfl⟩
    simp only [w, dif_pos h]
    exact h₁ _ _ h.choose_spec.symm
  have hw' : ∀ k, u' k = w (φ' k) := fun k => by
    by_cases h : ∃ l, φ l = φ' k
    · simp only [w, dif_pos h]
      exact (h₃ _ _ h.choose_spec).symm
    · have h' : ∃ l, φ' l = φ' k := ⟨k, rfl⟩
      simp only [w, dif_neg h, dif_pos h']
      exact h₂ _ _ h'.choose_spec.symm
  simp only [hw, hw']
  rw [prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ (fun k => by simp) ε w,
    prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ' (fun k => by simp) ε' w]
  simp only [hs]

section Frame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

set_option backward.isDefEq.respectTransparency false in

theorem origin_mem {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) {U : A.left.Opens}
    (p : Sp (Jet ℂ (Fin n × Fin g) m)) (hp : ψ p ∈ U) : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := h
  rw [Scheme.Hom.comp_apply, jet_point_eq (K := ℂ) (J := Fin 1 × Fin (n * g)) (m := m)
      (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) p),
    jetPt_closedPoint] at hp
  have hc : colsOf n g 0 = 0 := rfl
  rw [hc, map_zero] at hp
  exact top_le_of_mem hp

theorem fr_analyticAt (j : L.L.ι) (h : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j) : AnalyticAt ℂ (Φ.fr j) 0 :=
  GlobalTheory.SCV.analyticAt_of_differentiableOn (Φ.fr_hol j) ((Φ.hol (L.L.U j) 0).1.mem_nhds h)

end Frame

set_option backward.isDefEq.respectTransparency false in

theorem corr_of_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → LB.SameSum φ ε φ' ε' → LB.Gen.Corr L.L φ ε φ' ε' τ τ' := by
  intro S A _ _ L x0 g Φ hI n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h h' hs j j' c c' cc
  by_cases hW : ∃ p, p ∈ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j'
  · obtain ⟨p, hp⟩ := hW
    have hT : ⊤ ≤ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' := fun q _ => by
      have e1 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) p
      have e2 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) q
      rw [e2, ← e1]
      exact hp
    have o : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j k) := fun k =>
      origin_mem Φ (h.1 k) p (LB.wchart_le L.L φ j k hp.1)
    have o' : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' k) := fun k =>
      origin_mem Φ (h'.1 k) p (LB.wchart_le L.L φ' j' k hp.2)
    obtain ⟨u, hu, hP⟩ := jetN_prod_zpow m (fun k => Φ.fr (j k)) (fun k => fr_analyticAt Φ _ (o k))
      (fun k => Φ.fr_ne _ _ (o k)) Λ ε
    obtain ⟨u', hu', hP'⟩ := jetN_prod_zpow m (fun k => Φ.fr (j' k)) (fun k => fr_analyticAt Φ _ (o' k))
      (fun k => Φ.fr_ne _ _ (o' k)) Λ' ε'
    have hE : ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
      refine prod_zpow_eq φ ε φ' ε' u u' (fun k l e => Units.ext ?_) (fun k l e => Units.ext ?_)
        (fun k l e => Units.ext ?_) hs
      · rw [hu, hu, c k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ l) _ _ (e ▸ h.1 k) (h.1 l) _
      · rw [hu', hu', c' k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h'.1 k) (h'.1 l) _
      · rw [hu, hu', cc k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h.1 k) (h'.1 l) _
    have r := h.2 j (hT.trans inf_le_left)
    have r' := h'.2 j' (hT.trans inf_le_right)
    rw [hP, hE, ← hP', ← r'] at r
    apply Units.ext
    have r2 := congrArg ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map
      (homOfLE (le_top : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' ≤ ⊤)).op).hom r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp] at r2
    exact r2
  · have hB : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' = ⊥ := by
      rw [eq_bot_iff]
      exact fun p hp => (hW ⟨p, hp⟩).elim
    have : Subsingleton Γ(Sp (Jet ℂ (Fin n × Fin g) m), LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j') := by
      rw [hB]; infer_instance
    exact Units.ext (Subsingleton.elim _ _)

end GlobalTheory.AnVal.JetCorr
end
end

