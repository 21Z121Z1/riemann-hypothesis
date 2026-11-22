import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH

theorem gt_add_iota_sub_exist : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ g g' : GtPtF u.D.toPre (PadicAlgCl p), ∃ g'', GtPtF.IsAdd g g' g'') ∧ (∀ y, ∃ g : GtPtF u.D.toPre (PadicAlgCl p), GtPtF.IsIota y g) ∧ ∀ g h : GtPtF u.D.toPre (PadicAlgCl p), ∃ g', GtPtF.IsAdd g' h g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u
  letI := GlobalTheory.TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  exact ⟨fun g g' => ⟨g + g', (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl⟩,
    fun y => GlobalTheory.TorusExt.exists_iota u.D.tau_bimult y,
    fun g h => ⟨g - h, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (sub_add_cancel g h).symm⟩⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.PureWt

theorem cf_diag {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
    {f : A →+* R} {m : Multiplicative X →* R}
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (σ : R →+ R) (κ : X → A)
    (hσ : ∀ b ψ, σ (f b * m (Multiplicative.ofAdd ψ)) = f (κ ψ) * (f b * m (Multiplicative.ofAdd ψ)))
    (χ : X) (s : R) : WtPart.cf hb χ (σ s) = κ χ * WtPart.cf hb χ s := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, WtPart.cf_zero, mul_zero]
  | add x y hx hy => simp only [map_add, WtPart.cf_add, mul_add, hx, hy]
  | single ψ b =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, hσ, ← _root_.mul_assoc, ← map_mul, WtPart.cf_mono,
      WtPart.cf_mono]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

theorem exists_char_ne {k X K : Type} [Field k] [Infinite k] [AddCommGroup X] (b : Module.Basis K ℤ X)
    {χ α : X} (h : χ ≠ α) :
    ∃ t : Multiplicative X →* kˣ, t (Multiplicative.ofAdd χ) ≠ t (Multiplicative.ofAdd α) := by
  obtain ⟨i, hi⟩ : ∃ i, b.repr χ i ≠ b.repr α i := by
    by_contra hn
    push Not at hn
    exact h (b.repr.injective (Finsupp.ext hn))
  have hn : (b.repr χ i - b.repr α i).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 hi)
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x ^ (b.repr χ i - b.repr α i).natAbs ≠ 1 := by
    by_contra hc
    push Not at hc
    generalize (b.repr χ i - b.repr α i).natAbs = n at hn hc
    have : NeZero n := ⟨hn⟩
    have : Finite kˣ := Finite.of_surjective (fun x : rootsOfUnity n k => (x : kˣ))
      fun x => ⟨⟨x, (mem_rootsOfUnity n x).2 (hc x)⟩, rfl⟩
    have : Finite k := Finite.of_surjective (fun x : Option kˣ => x.elim (0 : k) Units.val) fun x => by
      by_cases hx : x = 0
      · exact ⟨none, hx.symm⟩
      · exact ⟨some (Units.mk0 x hx), rfl⟩
    exact not_finite k
  refine ⟨(zpowersHom kˣ x).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom), fun e => hx ?_⟩
  have e' : x ^ (b.repr χ i) = x ^ (b.repr α i) := e
  rw [pow_natAbs_eq_one, zpow_sub, e', mul_inv_cancel]

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

theorem translate_mem {Z : Over S} (τ : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (V : E.B.left.Opens) (z : Z.left)
    (hz : g.left z ∈ D.q.left ⁻¹ᵁ V) : ((τ ≫ D.i) * g).left z ∈ D.q.left ⁻¹ᵁ V :=
  haveI := D.q_hom
  GtBaseChange.translate_mem D.q D.i D.isKernel τ g V z hz

theorem gm_points {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd χ)) =
      gm τ.left z ⊤ (charUnit S X χ) := by
  apply Units.ext
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial, splitTorusPointsEquiv_val]
  rfl

theorem hasWt_mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) (c : Γ(E.B.left, V)) (χ : E.X) :
    UFib.HasWt D.i (D.q.left ⁻¹ᵁ V)
      ((D.q.left.app V).hom c * WtPart.mono D j V h (Multiplicative.ofAdd χ)) χ := by
  intro Z τ g z hz
  have hz' := translate_mem D τ g V z hz
  set v := AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom with hv
  let A : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ := (gm ((τ ≫ D.i) * g).left z _).comp v
  let C : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ :=
    (gm (𝟙 Z.left) z ⊤).comp (splitTorusPointsEquiv S E.X Z τ) * (gm g.left z _).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k) := by
      simp [hv]
    refine congrArg Additive.ofMul ?_
    change gm _ z _ (v (Multiplicative.ofAdd (E.basis k))) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))) *
        gm _ z _ (v (Multiplicative.ofAdd (E.basis k)))
    rw [hvk, gm_points, gm_res _ z _ hz, gm_res _ z _ hz']
    exact (GtBaseChange.hasWeight_iff D.i _ _ _ (D.act_le _) _).2 (D.equiv j k) Z τ g z (h hz)
  have e : gm ((τ ≫ D.i) * g).left z _ (v (Multiplicative.ofAdd χ)) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd χ)) *
        gm g.left z _ (v (Multiplicative.ofAdd χ)) :=
    congrArg (fun φ => Additive.toMul (φ χ)) hAC
  have em : WtPart.mono D j V h (Multiplicative.ofAdd χ) = (v (Multiplicative.ofAdd χ)).val := rfl
  rw [em, gs_mul _ z _ hz, gs_mul _ z _ hz', gs_unit _ z _ hz, gs_unit _ z _ hz', e, gm_points,
    gs_pull _ _ z V hz, gs_pull _ _ z V hz', TorusTranslate.translate_comp_q, Units.val_mul]
  ring

theorem translate_appLE (V : E.B.left.Opens) (τ : G ⟶ splitTorus S E.X)
    (hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (χ : E.X) (hs : UFib.HasWt D.i _ s χ) (a : Γ(S, ⊤))
    (ha : τ.left.appTop.hom (charUnit S E.X χ).val = G.hom.appTop.hom a) :
    (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s =
      (D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a) * s := by
  refine fn_ext fun z hz => ?_
  have e := hs G τ (𝟙 G) z hz
  have e₁ : gs (𝟙 G.left) z _ ((((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s) =
      gs ((τ ≫ D.i) * 𝟙 G).left z _ s :=
    (gs_res (𝟙 G.left) z hle hz _).trans ((gs_pull (𝟙 G.left) ((τ ≫ D.i) * 𝟙 G).left z (D.q.left ⁻¹ᵁ V) (hle hz) s).trans (by rw [Category.id_comp]))
  have e₂ : gs (𝟙 G.left) z _ ((D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a)) =
      gs G.hom z ⊤ a := by
    refine (gs_pull (𝟙 G.left) _ z V hz _).trans ((gs_res (𝟙 G.left ≫ D.q.left) z (U := E.B.hom ⁻¹ᵁ ⊤) le_top hz _).trans
      ((gs_pull _ E.B.hom z ⊤ trivial a).trans ?_))
    rw [Category.id_comp, Over.w]
  rw [e₁, e, gs_mul (𝟙 G.left) z (D.q.left ⁻¹ᵁ V) hz, e₂, gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  exact congrArg₂ (· * ·) (congrArg (G.left.presheaf.germ ⊤ z trivial).hom ha) rfl

theorem hasWt_iff_weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  intro k _ _ E G _ D j V hV h f α
  have hb := D.coord j V hV h
  constructor
  · intro hf χ hχ
    obtain ⟨t, ht⟩ := exists_char_ne (k := k) E.basis hχ
    let c : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    let e := splitTorusPointsEquiv (Sp k) E.X G
    let τ := e.symm ((Units.map (G.hom.appTop.hom.comp c).toMonoidHom).comp t)
    have hτ : ∀ ψ, τ.left.appTop.hom (charUnit (Sp k) E.X ψ).val =
        G.hom.appTop.hom (c (t (Multiplicative.ofAdd ψ))) := fun ψ => by
      rw [← splitTorusPointsEquiv_val]
      change (e (e.symm _) _).val = _
      rw [e.apply_symm_apply]
      rfl
    have hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) :=
      fun z hz => translate_mem D τ (𝟙 G) V z hz
    let κ : k →+* Γ(E.B.left, V) := (E.B.hom.appLE ⊤ V le_top).hom.comp c
    have e₁ := cf_diag hb (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom.toAddMonoidHom
      (fun ψ => κ (t (Multiplicative.ofAdd ψ)))
      (fun b ψ => translate_appLE D V τ hle _ ψ (hasWt_mono D j V h b ψ) _ (hτ ψ)) χ f
    have e₂ := cf_diag hb (AddMonoidHom.mulLeft ((D.q.left.app V).hom (κ (t (Multiplicative.ofAdd α)))))
      (fun _ => κ (t (Multiplicative.ofAdd α))) (fun _ _ => rfl) χ f
    have e₃ := e₁.symm.trans ((congrArg (WtPart.cf hb χ) (translate_appLE D V τ hle f α hf _ (hτ α))).trans e₂)
    rw [← sub_eq_zero, ← sub_mul, ← map_sub] at e₃
    exact ((IsUnit.mk0 _ (sub_ne_zero.2 fun e => ht (Units.ext e))).map κ).mul_right_eq_zero.1 e₃
  · intro hf
    have e : f = (D.q.left.app V).hom (WtPart.cf hb α f) * WtPart.mono D j V h (Multiplicative.ofAdd α) := by
      refine WtPart.cf_ext hb fun χ => ?_
      rw [WtPart.cf_mono]
      split_ifs with hχ
      · rw [hχ]
      · exact hf χ fun e => hχ e.symm
    rw [e]
    exact hasWt_mono D j V h _ α

end GlobalTheory.ZH.PureWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.InFibChart

theorem eval_scale {K J : Type} [CommRing K] (c : K) (x : J → K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    MvPolynomial.eval (fun j => c * x j) F = c ^ d * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_subst {K J : Type} [CommRing K] [Fintype J] (g : Matrix J J K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    ∃ F' : MvPolynomial J K, F'.IsHomogeneous d ∧
      ∀ v, MvPolynomial.eval v F' = MvPolynomial.eval (g.mulVec v) F := by
  refine ⟨MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) F, ?_, fun v => ?_⟩
  · have := hF.aeval (n := 1) (fun i => ∑ j, MvPolynomial.C (g i j) * (MvPolynomial.X j : MvPolynomial J K))
      (fun i => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using this
  · clear hF
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Matrix.mulVec, dotProduct]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

theorem hom_genericPoint (hU : (U₀ : Set M.Z).Nonempty) :
    Q.P.hom (genericPoint Q.P.left) = genericPoint M.Z := by
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hw : η[ρ.P.A].left ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  let s : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ η[ρ.P.A].left) (𝟙 _) (by
      rw [Category.assoc, Category.id_comp]; exact (congrArg (Q.u₀ ≫ ·) hw).trans (Category.comp_id _))
  have hs : (s ≫ Q.a₀) ≫ Q.P.hom = U₀.ι := by
    rw [Category.assoc, Q.cart.w, pullback.lift_snd_assoc, Category.id_comp]
  have h1 : Q.P.hom ((s ≫ Q.a₀) ⟨_, hg⟩) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : U₀.toScheme ⟶ M.Z => f ⟨_, hg⟩) hs)
  have h2 := (genericPoint_specializes ((s ≫ Q.a₀) ⟨_, hg⟩)).map Q.P.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem exists_change (l l' : Q.Λ) {z : M.Z} (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l') :
    ∃ g : Matrix S.J S.J (M.O z), Q.B l' = g.map (↑) * Q.B l ∧
      (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑) := by
  have h : ∀ i, ∃ a : S.J → M.O z, ∑ j, a j • Q.B l j = Q.B l' i := fun i => by
    refine (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => Q.B l j k)).1 ?_
    refine (Q.basis l z hl).le ((Q.basis l' z hl').ge ?_)
    exact Submodule.subset_span ⟨i, rfl⟩
  choose a ha using h
  have e : Q.B l' = (Matrix.of a).map (↑) * Q.B l := by
    ext i k
    rw [← ha i]
    simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]
  refine ⟨Matrix.of a, e, ?_⟩
  have h1 := mul_eq_one_comm.1 (Q.c_inv l)
  have h2 := Q.c_inv l'
  rw [e] at h2
  calc _ = ((Q.c l').map (valF M.pt (Q.W l')) * ((Matrix.of a).map (↑) * Q.B l)) *
        (Q.c l).map (valF M.pt (Q.W l)) := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem crd_change_loc (l l' : Q.Λ) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (y' : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp R ⟶ M.Z)
    (hy : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t) (q : Sp R) (hq : t q = genericPoint M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint R) ⤳ z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → R} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') y' w') :
    ∃ u : Rˣ, ∀ j, w' j = (u : R) * (g.map (RatModel.valLoc t z hz)).mulVec w j := by
  have ht' : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by
    rw [← Category.assoc, hy, Category.assoc, ht]
  have h1 := Q.rel l R y w hw
  have h2 := Q.rel l' R y' w' hw'
  rw [ht] at h1
  rw [ht', hy] at h2
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h1 h2
  refine ⟨u, ?_⟩
  let C : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl (Q.c l i j)⟩
  let C' : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl' (Q.c l' i j)⟩
  have hC : C = C' * g := by
    ext i j
    have := congrFun (congrFun hg i) j
    simpa [Matrix.mul_apply, C, C'] using this
  have e1 : (Q.c l).map (valR t (Q.W l)) = C.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl _).symm
  have e2 : (Q.c l').map (valR t (Q.W l')) = C'.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl' _).symm
  have hW : ⊤ ≤ t ⁻¹ᵁ Q.W l' := (CrdCalc.top_le_iff t _).2 (hz.mem_open (Q.W l').isOpen hl')
  have hdet : ((Q.c l').map (valR t (Q.W l'))).det ≠ 0 := by
    have e3 : (Q.c l').map (valR t (Q.W l')) = (CrdCalc.valHom t _ hW).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq t _ hW _
    rw [e3, ← RingHom.map_det]
    intro h0
    have hpt : ⊤ ≤ M.pt ⁻¹ᵁ Q.W l' := M.top_le_preimage_pt (Q.ne l')
    have e4 : (Q.c l').map (valF M.pt (Q.W l')) = (CrdCalc.valHom M.pt _ hpt).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq M.pt _ hpt _
    have h5 : IsUnit (valR M.pt (Q.W l') (Q.c l').det) := by
      rw [CrdCalc.valR_eq M.pt _ hpt, RingHom.map_det, ← e4]
      exact Matrix.isUnit_det_of_right_inverse (Q.c_inv l')
    have h6 : genericPoint M.Z ∈ M.Z.basicOpen (Q.c l').det := by
      rw [← M.pt_apply (IsLocalRing.closedPoint Ω)]
      exact (CrdCalc.isUnit_valR_iff M.pt _ hpt _).1 h5 (Set.mem_univ _)
    have h7 : (t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det = 0 :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (h0.trans (map_zero _).symm)
    have b := Scheme.basicOpen_appLE t ⊤ (Q.W l') hW (Q.c l').det
    have h8 : q ∈ (Sp R).basicOpen ((t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det) :=
      b.ge ⟨trivial, show t q ∈ _ from hq ▸ h6⟩
    rw [h7, Scheme.basicOpen_zero] at h8
    exact h8
  have h9 : ((Q.c l').map (valR t (Q.W l'))).mulVec
      (w' - (u : R) • (g.map (RatModel.valLoc t z hz)).mulVec w) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, sub_eq_zero]
    funext j
    rw [hu j, e1, e2, hC, Matrix.map_mul]
    rfl
  have h10 := sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hdet h9)
  intro j
  rw [h10]
  rfl

theorem crd_change (hU : (U₀ : Set M.Z).Nonempty) (l l' : Q.Λ) {K : Type} [Field K]
    (x : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp K ⟶ M.Z)
    (hx : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → K} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') x' w') :
    ∃ u : K, w' = fun j => u * (g.map fun a => M.val t a).mulVec w j := by
  obtain ⟨X, hX⟩ : ∃ X : Sp K ⟶ Q.P.left, X = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι := ⟨_, rfl⟩
  have hXt : X ≫ Q.P.hom = t := by rw [hX, Category.assoc, ht]
  let p : Q.P.left := X (IsLocalRing.closedPoint K)
  have hp : Q.P.hom p = z := by
    rw [← hz, ← hXt]
    exact (Scheme.Hom.comp_apply _ _ _).symm
  let R : Type := Q.P.left.presheaf.stalk p
  let Y : Sp R ⟶ Q.P.left := Q.P.left.fromSpecStalk p
  let φ : R →+* K := (Scheme.stalkClosedPointTo (R := .of K) X).hom
  have hφ : spMap φ ≫ Y = X := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) X
  have hr : Set.range Y = {ξ | ξ ⤳ p} := Scheme.range_fromSpecStalk
  have hlift : ∀ k : Q.Λ, z ∈ Q.W k → ∃ y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W k).toScheme,
      y ≫ (Q.P.hom ⁻¹ᵁ Q.W k).ι = Y := fun k hk =>
    ⟨IsOpenImmersion.lift _ Y (by
      rw [Scheme.Opens.range_ι, hr]
      exact fun ξ hξ => Specializes.mem_open hξ (Q.P.hom ⁻¹ᵁ Q.W k).isOpen (show Q.P.hom p ∈ Q.W k from hp ▸ hk)),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨y, hy⟩ := hlift l hl
  obtain ⟨y', hy'⟩ := hlift l' hl'
  have hxy : spMap φ ≫ y = x := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l).ι, Category.assoc, hy, hφ, hX]
  have hxy' : spMap φ ≫ y' = x' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l').ι, Category.assoc, hy', hφ, hX, hx]
  obtain ⟨q, hq⟩ : genericPoint Q.P.left ∈ Set.range Y := hr ▸ genericPoint_specializes p
  have hq' : (Y ≫ Q.P.hom) q = genericPoint M.Z := by
    rw [Scheme.Hom.comp_apply, hq, hom_genericPoint Q hU]
  have hc : (Y ≫ Q.P.hom) (IsLocalRing.closedPoint R) ⤳ z := by
    have : Y (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
    exact specializes_of_eq ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg Q.P.hom this).trans hp))
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y
  obtain ⟨v', hv'⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l') y'
  obtain ⟨u, hu⟩ := crd_change_loc Q l l' y y' (Y ≫ Q.P.hom) (hy'.trans hy.symm)
    (by rw [← Category.assoc, hy]) q hq' hc hl hl' g hg hv hv'
  have k1 := CrdCalc.crd_map φ hv
  have k2 := CrdCalc.crd_map φ hv'
  rw [hxy] at k1
  rw [hxy'] at k2
  obtain ⟨a, ha⟩ := CrdCalc.crd_unique hw k1
  obtain ⟨b, hb⟩ := CrdCalc.crd_unique k2 hw'
  refine ⟨b * φ u * a, funext fun j => ?_⟩
  have hval : ∀ c : M.O z, φ (RatModel.valLoc (Y ≫ Q.P.hom) z hc c) = M.val t c := fun c => by
    rw [← RatModel.val_spMap_comp, ← Category.assoc, hφ, hXt]
  rw [hb j]
  simp only [hu j, map_mul, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, hval, ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem tors_change (hB : BaseFacts S M U₀ EE) (l l' : Q.Λ) {K : Type} [Field K] (t : Sp K ⟶ M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l)
    (g : Matrix S.J S.J (M.O z)) (hg : Q.B l' = g.map (↑) * Q.B l) {v : S.J → K} (hv : v ∈ Q.Tors t l) :
    (g.map fun a => M.val t a).mulVec v ∈ Q.Tors t l' := by
  obtain ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, rfl⟩ := hv
  have hzz : z' = z := by rw [← hw, ← hz, Subsingleton.elim w (IsLocalRing.closedPoint K)]
  subst hzz
  refine ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, funext fun i => ?_⟩
  have hr : Set.range t = {z'} := hw ▸ RatModel.range_eq_singleton t w
  let a : S.J → M.O z' := fun j => ⟨(Q.B l j ⬝ᵥ S.ev h) / S.th x₀,
    (hB.sec z' x₀ hx₀ h hh).1 _ ((Q.basis l z' hl).ge (Submodule.subset_span ⟨j, rfl⟩))⟩
  have e : (Q.B l' i ⬝ᵥ S.ev h) / S.th x₀ = ((∑ j, g i j * a j : M.O z') : Ω) := by
    have e1 : Q.B l' i ⬝ᵥ S.ev h = (Q.B l').mulVec (S.ev h) i := rfl
    rw [e1, hg, ← Matrix.mulVec_mulVec]
    simp [a, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
  rw [e, ← RatModel.valHom_apply t z' hr, map_sum]
  simp only [map_mul, RatModel.valHom_apply]
  rfl

theorem inFib_of_chart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (l : Q.Λ) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → (∀ (d : ℕ) (Pf : MvPolynomial S.J K), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d → (∀ v ∈ Q.Tors (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) l, MvPolynomial.eval v Pf = 0) → MvPolynomial.eval w Pf = 0) → Q.InFib (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ l x w hw H l' x' w' hx hw' d Pf hd hPf hT
  rw [Category.assoc] at hT
  obtain ⟨t, ht⟩ : ∃ t, x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t := ⟨_, rfl⟩
  have ht' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by rw [← Category.assoc, hx, Category.assoc, ht]
  rw [ht] at hT H
  have hl : t (IsLocalRing.closedPoint K) ∈ Q.W l := by
    rw [← ht]
    exact (x (IsLocalRing.closedPoint K)).2
  have hl' : t (IsLocalRing.closedPoint K) ∈ Q.W l' := by
    rw [← ht']
    exact (x' (IsLocalRing.closedPoint K)).2
  obtain ⟨g, hg, hc⟩ := exists_change Q l l' hl hl'
  obtain ⟨u, rfl⟩ := crd_change Q hB.ov.ne l l' x x' t hx ht rfl hl hl' g hc hw hw'
  obtain ⟨F, hF, hev⟩ := exists_subst (g.map fun a => M.val t a) hPf
  have h0 := H d F hd hF fun v hv => by
    rw [hev]
    exact hT _ (tors_change Q hB l l' t rfl hl g hg hv)
  rw [eval_scale u _ hPf, ← hev, h0, mul_zero]

end GlobalTheory.ZH.InFibChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

def kf (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kf_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Bijective (kf R F) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem base_eq : (show (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left from spMap y₀) ≫
    (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
  refine (Category.comp_id _).trans ?_
  exact (congrArg spMap u.fac.symm).trans
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p))))

def Moved (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)) {k : ℕ} (t : SecA u.A (PadicAlgCl p) k)
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : Prop :=
  ThetaPtMove.SecRel u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w t s

theorem exists_moved {w : LB.Iso u.A.L (ρ.P.L.pull u.φ)} (hw : w.IsGen) {k : ℕ}
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : ∃ t, Moved u w t s :=
  ThetaPtMove.exists_secRel u.cart _ _ hw ρ.P.isLB u.A.isLB s

end GlobalTheory.ZH.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointExtendsTorsionPointMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.modelPointExtendsTorsionPoint_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G), GlobalTheory.UnitTheta.Extends u a h → GlobalTheory.UnitTheta.Extends u b h' → GlobalTheory.UnitTheta.Extends u (a + b) (h * h') := by
  first | exact @GlobalTheory.UnitTheta.extends_mul | exact GlobalTheory.UnitTheta.extends_mul | (intros; apply GlobalTheory.UnitTheta.extends_mul <;> assumption)
end

