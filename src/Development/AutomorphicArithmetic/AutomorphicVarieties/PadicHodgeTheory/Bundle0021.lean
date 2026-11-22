import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0020

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ConjugateRestrictionOpenNormal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (c : G →* G)
    (hc : Function.Surjective c) (ρ : Representation A G V) :
    IsCr (φ.comp c) (ρ.comp c : Representation A G V) ↔ IsCr φ ρ := by
  have hr : (φ.comp c).range = φ.range := by
    ext σ
    refine ⟨fun ⟨g, hg⟩ => ⟨c g, hg⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨g, rfl⟩ := hc g
    exact ⟨g, hg⟩
  have hd : Dcr (φ.comp c) (resCoef ℚ_[l] (ρ.comp c : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hc.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold IsCr
  rw [hr, hd]

private theorem conj_left {B : Type} [CommRing B] (w : GG 3 B) (x y : GL (Fin 3) B)
    (h : GG.ofGL y = w * GG.ofGL x * w⁻¹) : y = w.left * sgnAct 3 B w.right x * w.left⁻¹ := by
  have := congrArg SemidirectProduct.left h
  have e : sgnAct 3 B w.right (sgnAct 3 B w.right w.left) = w.left := by
    rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]
  simpa [e] using this

private theorem dot_inv {B : Type} [CommRing B] (a m : GL (Fin 3) B) (u x : Fin 3 → B) :
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec
      (((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec u))
      ((m : Matrix (Fin 3) (Fin 3) B).mulVec x) =
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec u) x := by
  have e : Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) *
      ((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).transpose *
        (Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
      theta_val]
    simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec x, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.conjugate_restriction_open_normal :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (H : Subgroup (GQ l)) [H.Normal], IsOpen (H : Set (GQ l)) → ∀ (ρ ρ' : ↥H →* GL (Fin 3) B), Continuous (fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)) → ∀ (s : GQ l) (w : GG 3 B), (∀ g g' : H, (g' : GQ l) = s⁻¹ * g * s → GG.ofGL (ρ' g) = w * GG.ofGL (ρ g') * w⁻¹) → IsCr H.subtype (colRep ρ) → IsCr H.subtype (colRep ρ') := by
  intro l _ B _ _ _ _ _ _ H hN hH ρ ρ' hρ s w hw hcr
  have hψ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  let c : H →* H := (MulAut.conjNormal (H := H) s⁻¹).toMonoidHom
  have hc : ∀ g : H, (c g : GQ l) = s⁻¹ * g * s := fun g => by
    change ((MulAut.conjNormal (H := H) s⁻¹ g : H) : GQ l) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ c = fun g : H => s⁻¹ * (g : GQ l) * s := funext hc
    rw [this]
    fun_prop
  let σ : H →* GL (Fin 3) B := ρ.comp c
  have hσ : Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) B)) := hρ.comp hcc
  have hσi : Continuous (fun g => (((σ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    simp only [← map_inv]
    exact hσ.comp continuous_inv
  have hσcr : IsCr H.subtype (colRep σ) := by
    have h1 := (isCr_comp H.subtype c (MulAut.conjNormal (H := H) s⁻¹).surjective (colRep ρ)).2 hcr
    have h2 : H.subtype.comp c = (MulAut.conj s⁻¹).toMonoidHom.comp H.subtype := by
      refine MonoidHom.ext fun g => ?_
      change (c g : GQ l) = s⁻¹ * g * s⁻¹⁻¹
      rw [hc, inv_inv]
    rw [h2] at h1
    exact (admissible_conjugate H.subtype hψ (colRep σ) s⁻¹).1.1 h1
  have he : ∀ g, ρ' g = w.left * sgnAct 3 B w.right (σ g) * w.left⁻¹ := fun g =>
    conj_left w _ _ (hw g (c g) (hc g))
  generalize w.left = a at he
  rcases Int.units_eq_one_or w.right with h | h
  · simp only [h, sgnAct_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul]
      exact (continuous_const.matrix_mul hσ).matrix_mul continuous_const
    refine ((isCrys_isDR_sub_quot H.subtype hψ (colRep σ) (colRep ρ') (contAction_colRep hσ) (contAction_colRep hρ')
      ((Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) (fun g x => ?_)).2
      (fun v => ?_)).1 hσcr
    · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, he,
        ← Units.val_mul, inv_mul_cancel_right]
    · refine ⟨((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec v, ?_⟩
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · simp only [h, sgnAct_neg_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul, theta_val]
      exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hσi.matrix_transpose).matrix_mul
        continuous_const)).matrix_mul continuous_const
    have c1 : ContAction (chRep (1 : H →* Bˣ)) := contAction_chRep continuous_const
    have cr1 : IsCr H.subtype (chRep (1 : H →* Bˣ)) :=
      crUnr (A := ℚ_[l]) H.subtype hψ (resCoef ℚ_[l] (chRep (1 : H →* Bˣ))) c1 0
        (fun g _ x => by simp [resCoef, chRep])
    let N : Matrix (Fin 3) (Fin 3) B := Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
    refine (isCrys_isDR_internalHom H.subtype hψ (colRep σ) (chRep (1 : H →* Bˣ)) (colRep ρ') (contAction_colRep hσ) c1
      (contAction_colRep hρ')
      (LinearMap.mk₂ ℚ_[l] (fun (u x : Fin 3 → B) => dotProduct (N.mulVec u) x)
        (fun _ _ _ => by rw [Matrix.mulVec_add, add_dotProduct])
        (fun _ _ _ => by rw [Matrix.mulVec_smul, smul_dotProduct])
        (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _))
      (fun g u x => ?_) (fun u u' huu => ?_)).1 hσcr cr1
    · simp only [LinearMap.mk₂_apply, colRep_apply, chRep_apply, MonoidHom.one_apply, Units.val_one, one_mul]
      rw [he]
      exact dot_inv a (σ g) u x
    · have h1 : N.mulVec u = N.mulVec u' := by
        funext i
        have := LinearMap.congr_fun huu (Pi.single i 1)
        simpa only [LinearMap.mk₂_apply, dotProduct_single, mul_one] using this
      have h2 : ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3) * N = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat B 3), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]
      have h3 := congrArg ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3).mulVec h1
      simpa only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsContinuousIsGamOfTorusCocycle
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem gam_cocycle {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B)
    (β : G → B × B) (hβ : ∀ g g', β (g * g') = β g + T.M1 g (β g')) (a b c : G) :
    (T.χ2 a : B) * (-(h * omg (β b) (T.M1 b (β c)))) - (-(h * omg (β (a * b)) (T.M1 (a * b) (β c))))
      + (-(h * omg (β a) (T.M1 a (β (b * c))))) - (-(h * omg (β a) (T.M1 a (β b)))) = 0 := by
  have e := T.alternatingForm_adjointSuperdiagRep a (β b) (T.M1 b (β c))
  rw [hβ a b, hβ b c, map_mul, Module.End.mul_apply, map_add]
  generalize T.M1 a (T.M1 b (β c)) = u at e ⊢
  generalize T.M1 a (β b) = w at e ⊢
  simp only [omg, Prod.fst_add, Prod.snd_add] at e ⊢
  linear_combination h * e

theorem UpperTheory.exists_continuous_isGam_of_torus_cocycle :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), ∀ β ∈ Z1 T.M1, ∃ γ : GQ l → B, Continuous γ ∧ T.IsGam h β γ := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β hβ
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  have hχ := Tor.continuous_χ2 hD.ηlc T hT.cont hT.cont_inv
  have hM := Tor.contAction_torus_module hD.ηlc T hT.cont hT.cont_inv
  have hρ : ContAction (resCoef E (chRep T.χ2)) := contAction_chRep hχ
  obtain ⟨-, f2, -, e2⟩ := tateRat hP (v := l) (l := l) (MonoidHom.id (GQ l)) IsOpenEmbedding.id
    (resCoef E (chRep T.χ2)) hρ
  obtain ⟨s, hs, hsi⟩ := ((cycInertia l).2 H hD.isOpen).2
  have hsH : s ∈ H := hs.1
  have hsI : s ∈ Iq l := hs.2
  have hχs : (T.χ2 s : B) = algebraMap E B ((cycA l l E s ^ (2 * e) : Eˣ) : E) := by
    have h0 := hT.ine s hsI 0
    have h2 := hT.ine s hsI 2
    have w0 : wt1 (0 : Fin 3) = 1 := by decide
    have w2 : wt1 (2 : Fin 3) = -1 := by decide
    rw [w0, zpow_one] at h0
    rw [w2, zpow_neg_one] at h2
    have k0 : T.t s 0 = Units.map (algebraMap E B : E →* B) (Ψ s) := Units.ext h0
    have k2 : T.t s 2 = Units.map (algebraMap E B : E →* B) (Ψ s)⁻¹ := Units.ext h2
    rw [Tor.χ2_apply, hD.ηH s hsH, k0, k2, ← map_div, div_inv_eq_mul, hD.ΨH s hsH hsI, ← pow_add, ← two_mul]
    simp
  have hne : ((cycA l l E s ^ (2 * e) : Eˣ) : E) ≠ (cycA l l E s : E) := by
    intro hc
    apply hsi
    have h1 : cycA l l E s ^ (2 * e - 1) = 1 := by
      have := Units.ext hc
      have he := hD.e_pos
      rw [show 2 * e = (2 * e - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.1 this
    have inj : Function.Injective (algebraMap ℤ_[l] E) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e - 1, by have := hD.e_pos; omega, ?_⟩
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) inj
    rw [map_pow, map_one]
    exact h1
  have hbot : H0dual ((cycA l l E).comp (MonoidHom.id (GQ l))) (resCoef E (chRep T.χ2)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have h1 : f ((T.χ2 s : B) * x) = (cycA l l E s : E) * f x := hf s x
    rw [hχs, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 (show (_ - _) * f x = 0 by rw [sub_mul, h1, sub_self])).resolve_left (sub_ne_zero.2 hne)
  rw [hbot, finrank_bot] at e2
  haveI := f2
  have hsub : Subsingleton (H2 (resCoef E (chRep T.χ2))) := Module.finrank_zero_iff.1 e2
  have hc : Continuous fun p : GQ l × GQ l => -(h * omg (β p.1) (T.M1 p.1 (β p.2))) := by
    have a1 : Continuous fun p : GQ l × GQ l => β p.1 := hβ.1.comp continuous_fst
    have a2 : Continuous fun p : GQ l × GQ l => T.M1 p.1 (β p.2) :=
      hM.comp (continuous_fst.prodMk (hβ.1.comp continuous_snd))
    exact (continuous_const.mul ((a1.fst.mul a2.snd).sub (a1.snd.mul a2.fst))).neg
  let z : Z2 (resCoef E (chRep T.χ2)) := ⟨fun p => -(h * omg (β p.1) (T.M1 p.1 (β p.2))), hc,
    fun a b c => gam_cocycle T h β hβ.2 a b c⟩
  have hz : z ∈ (B2 (resCoef E (chRep T.χ2))).comap (Z2 (resCoef E (chRep T.χ2))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨γ, hγ, hγ2⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz
  refine ⟨γ, hγ, fun g g' => ?_⟩
  have h1 : (T.χ2 g : B) * γ g' - γ (g * g') + γ g = -(h * omg (β g) (T.M1 g (β g'))) := congrFun hγ2 (g, g')
  linear_combination -h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusPowEigenvectorMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem shift_prod {R : Type} [CommMonoid R] (a : ℕ → R) (f : ℕ) :
    (∏ i ∈ Finset.range f, a (i + 1)) * a 0 = (∏ i ∈ Finset.range f, a i) * a f := by
  rw [← Finset.prod_range_succ', Finset.prod_range_succ]

private theorem descend {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [IsDomain B]
    (PD : PeriodData G Qp K₀ K B BdR) (f : ℕ) (hσ : ∀ x, (PD.σ ^ f) x = x) (b : B) (δ : K₀) (hb : b ≠ 0)
    (hφ : (PD.φ ^ f) b = algebraMap K₀ B δ * b) (hF : ∀ i : ℕ, PD.ι ((PD.φ ^ i) b) ∈ PD.Fil 0) :
    ∃ (c : B) (x : Qp), c ≠ 0 ∧ PD.φ c = algebraMap Qp B x * c ∧ PD.ι c ∈ PD.Fil 0 ∧
      algebraMap Qp K₀ x = ∏ i ∈ Finset.range f, (PD.σ ^ i) δ := by
  have hinj : ∀ (i : ℕ) (y : B), y ≠ 0 → (PD.φ ^ i) y ≠ 0 := by
    intro i y hy h
    apply hy
    have h1 : Function.Injective (PD.φ ^ i) := by
      rw [AlgHom.coe_pow]; exact PD.φ_inj.iterate i
    exact h1 (h.trans (map_zero _).symm)
  have hK : ∀ (i : ℕ) (y : K₀), (PD.φ ^ i) (algebraMap K₀ B y) = algebraMap K₀ B ((PD.σ ^ i) y) := by
    intro i y
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, PD.φ_K₀]
  have hprod : ∀ a : ℕ → B, (∀ i, PD.ι (a i) ∈ PD.Fil 0) → PD.ι (∏ i ∈ Finset.range f, a i) ∈ PD.Fil 0 := by
    intro a ha
    rw [map_prod]
    exact Finset.prod_induction _ (fun y => y ∈ PD.Fil 0)
      (fun y z hy hz => by simpa using PD.Fil_mul 0 0 y z hy hz) PD.one_mem fun i _ => ha i
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hinj f b hb (by rw [hφ, map_zero, zero_mul])
  set c := ∏ i ∈ Finset.range f, (PD.φ ^ i) b with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hinj i b hb
  have hφc : PD.φ c = algebraMap K₀ B δ * c := by
    apply mul_right_cancel₀ hb
    have h := shift_prod (fun i => (PD.φ ^ i) b) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hc, hφ] at h
    rw [h]; ring
  set N := ∏ i ∈ Finset.range f, (PD.σ ^ i) δ with hN
  have hσN : PD.σ N = N := by
    apply mul_right_cancel₀ hδ
    have h := shift_prod (fun i => (PD.σ ^ i) δ) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hN, hσ] at h
    exact h
  obtain ⟨x, hx⟩ := PD.fund (algebraMap K₀ B N) (by rw [PD.φ_K₀, hσN]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∏ i ∈ Finset.range f, (PD.φ ^ i) c, x, Finset.prod_ne_zero_iff.2 fun i _ => hinj i c hc0, ?_,
    hprod _ fun i => ?_, ?_⟩
  · rw [hx, hN, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hφc, map_mul, hK]
  · rw [hc, map_prod]
    refine hprod _ fun j => ?_
    rw [← AlgHom.mul_apply, ← pow_add]
    exact hF _
  · rw [IsScalarTower.algebraMap_apply Qp K₀ B] at hx
    exact (algebraMap K₀ B).injective hx

private theorem norm_algHom' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (Om l)}
    (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ (b : Bcr l) (δ : ↥(K0 K)), b ≠ 0 → ((PP l).φB)^[f] b = algebraMap ↥(K0 K) (Bcr l) δ * b → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] b) ∈ ((PP l).PD (botExt l)).Fil 0) → ‖(δ : Om l)‖ ≤ 1 := by
  intro l _ K f hf hσ b δ hb hφ hF
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ((PP l).PD K).φ = (PP l).φB := AlgHom.ext ((PP l).PD_φ K)
  have hFil : ∀ y, y ∈ ((PP l).PD K).Fil 0 ↔ y ∈ ((PP l).PD (botExt l)).Fil 0 := fun y => by
    rw [← SetLike.mem_coe, (PP l).PD_Fil K (botExt l), SetLike.mem_coe]
  obtain ⟨c, x, hc, hφc, hFc, hx⟩ := descend ((PP l).PD K) f (fun y => by rw [AlgHom.coe_pow, hσ]) b δ hb
    (by rw [e, AlgHom.coe_pow, hφ]) (fun i => by rw [e, AlgHom.coe_pow, (PP l).PD_ι, hFil]; exact hF i)
  rw [e] at hφc
  rw [(PP l).PD_ι, hFil] at hFc
  have h1 := UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero c x hc hφc hFc
  have h2 := congrArg (fun y : ↥(K0 K) => ‖(K0 K).val y‖) hx
  simp only [map_prod, norm_prod, AlgHom.commutes] at h2
  have h3 : ∀ i : ℕ, ‖(K0 K).val ((((PP l).PD K).σ ^ i) δ)‖ = ‖(δ : Om l)‖ :=
    fun i => norm_algHom' ((K0 K).val.comp (((PP l).PD K).σ ^ i)) δ
  simp only [h3] at h2
  rw [Finset.prod_const, Finset.card_range, norm_algebraMap'] at h2
  rw [h2] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hf.ne').1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.prF :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0dual ((cycA l l E).comp φ) ρ = ⊥ → UpperTheory.V.Loc.finiteCocycles φ ρ = Z1 ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hpos hd
  obtain ⟨h0, -, -, hf⟩ := UpperTheory.V.Loc.posBasic hP φ hφ ρ hc hpos
  obtain ⟨hfin, -, h1, h2⟩ := UpperTheory.V.Loc.tateRat (v := l) (l := l) hP φ hφ ρ hc
  have hB := (UpperTheory.V.Loc.z1fMap φ ρ ρ).1 hc
  rw [hd, finrank_bot] at h2
  rw [h0, finrank_bot, h2, if_pos rfl, zero_add, zero_add] at h1
  have htop : finiteCohomology φ ρ = ⊤ := Submodule.eq_top_of_finrank_eq (hf.trans h1.symm)
  refine le_antisymm (fun c hc' => hc'.1) (fun c hc' => ?_)
  have hm : (Submodule.mkQ _ (⟨c, hc'⟩ : ↥(ReciprocityTheory.Gal.Z1 ρ)) : ReciprocityTheory.Gal.H1 ρ) ∈ finiteCohomology φ ρ := by
    rw [htop]; trivial
  obtain ⟨y, hy, hyc⟩ := hm
  have hsub := (Submodule.Quotient.eq _).1 hyc
  have h3 : (y : G → V) - c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := hB hsub
  have h4 := (UpperTheory.V.Loc.finiteCocycles φ ρ).sub_mem hy h3
  simpa using h4
end

