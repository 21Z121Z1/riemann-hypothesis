import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.LSeq

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem lpow_nzd (n : ℕ) : (l : A.Acr0) ^ n ∈ nonZeroDivisors A.Acr0 :=
  pow_mem (A.acris_torsion_free l (Fact.out : l.Prime).ne_zero) n

set_option synthInstance.maxHeartbeats 400000 in

def alphaL (n : ℕ) : A.Acr0 →ₗ[A.Acr0] (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ (n + 1)}) :=
  (Submodule.mkQ _).comp (LinearMap.mulLeft A.Acr0 ((l : A.Acr0) ^ n))

set_option synthInstance.maxHeartbeats 400000 in

def alpha (n : ℕ) : A.Acr 1 →+ A.Acr (n + 1) :=
  ((Ideal.span {(l : A.Acr0) ^ 1}).liftQ (alphaL A n) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker]
    simp only [alphaL, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)).toAddMonoidHom

theorem alpha_mk (n : ℕ) (y : A.Acr0) :
    alpha A n (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y) := rfl

theorem alpha_injective (n : ℕ) : Function.Injective (alpha A n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr 1 y = x := Ideal.Quotient.mk_surjective x
  rw [alpha_mk] at hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have h0 : (l : A.Acr0) ^ n * (y - c * (l : A.Acr0) ^ 1) = 0 := by
    rw [mul_sub, ← hc]; ring
  have h1 := mem_nonZeroDivisors_iff_left.1 (lpow_nzd A n) _ h0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, (sub_eq_zero.1 h1).symm⟩)

theorem alpha_exact (n : ℕ) : Function.Exact (alpha A n) (A.red n.le_succ) := by
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr (n + 1) y = x := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact ⟨A.mkAcr 1 c, by rw [alpha_mk, ← hc, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ : ∃ w, A.mkAcr 1 w = z := Ideal.Quotient.mk_surjective z
    rw [← red_mk A n.le_succ y, ← hz, alpha_mk, red_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨w, mul_comm _ _⟩)

theorem racrSeq (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcrSeq l :=
  fun n => ⟨fun A => alpha A n, fun A y => alpha_mk A n y, fun A => ⟨alpha_injective A n, alpha_exact A n⟩⟩

end GlobalTheory.CompanionTheory.LSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagatesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_property_propagates : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  first | exact @GlobalTheory.CompanionTheory.ConeSite.wK_rel | exact GlobalTheory.CompanionTheory.ConeSite.wK_rel | (intros; apply GlobalTheory.CompanionTheory.ConeSite.wK_rel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FramedSite

theorem cohomology_subsingleton_of_frame_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}
    (E : Frame Φ 0) (F : C ⥤ ModuleCat.{0} R) (hD : Subsingleton (F.obj E.D)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D (Frame.initial E)
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end GlobalTheory.CompanionTheory.FramedSite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cohomology

theorem subsingleton_H_of_ses {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (hi : ∀ T, Function.Injective (α.app T).hom)
    (he : ∀ T, Function.Exact (α.app T).hom (β.app T).hom)
    (hs : ∀ T, Function.Surjective (β.app T).hom)
    (h₂ : ∀ n, Subsingleton (CH.H F₂ n)) (h₃ : ∀ n, Subsingleton (CH.H F₃ n)) :
    ∀ n, Subsingleton (CH.H F₁ n) := by
  obtain ⟨c₁, c₂, c₃⟩ := CrystallineSemistableComparison.P.ses_cochains α β hi he hs
  obtain ⟨δ, -, hinj, -, -, hex⟩ :=
    CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  | succ n =>
    haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1)
    haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n
    have key : ∀ x : (CH.cx F₁).H (n + 1), x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hex n x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.CompanionTheory.Cohomology
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependentStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_cocycle_class_independent : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → ∀ (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0), (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcls.main | exact GlobalTheory.CompanionTheory.ConeZcls.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcls.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeZcoc

theorem plogK_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (s : ℕ)
    {x : B} (hx : x ∈ J) : f (plogK δ s x) = plogK δ' s (f x) := by
  unfold plogK
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, ← hf.2 x hx]

theorem units_cancel {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * c⁻¹) * (c * d * e⁻¹) = (b * d * f⁻¹) * (a * f * e⁻¹) := by
  have h1 : (a * b * c⁻¹) * (c * d * e⁻¹) = a * b * d * e⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : (b * d * f⁻¹) * (a * f * e⁻¹) = (a * b * d) * e⁻¹ * (f⁻¹ * f) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2, inv_mul_cancel, mul_one]

theorem plogK_four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (hs : pdP δ s = ⊥)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J)
    (hd : d - 1 ∈ J) (h : a * b = c * d) :
    plogK δ s (a - 1) + plogK δ s (b - 1) = plogK δ s (c - 1) + plogK δ s (d - 1) := by
  rw [← GlobalTheory.T.truncated_log_multiplicative δ s hs hu ha hb, ← GlobalTheory.T.truncated_log_multiplicative δ s hs hu hc hd]
  simp only [add_sub_cancel]
  rw [h]

theorem add_eq {B : Type} [CommRing B] {a c d b a' c' d' b' : B} (h₁ : a = a') (h₂ : c = c') (h₃ : d = d')
    (h₄ : b = b') (h : a' + c' = d' + b') : a + c = d + b := by
  rw [h₁, h₂, h₃, h₄, h]

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def rr (Λ : CLiftK g D) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c) : (g.obj c).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem r_eq (Λ : CLiftK g D) (σ : ComposableArrows C 2) :
    Λ.r σ = rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) := rfl

theorem rr_coboundary (Λ : CLiftK g D) {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃)
    (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f₀₃ : c₀ ⟶ c₃) (h₀₂ : f₀₂ = f₀₁ ≫ f₁₂) (h₁₃ : f₁₃ = f₁₂ ≫ f₂₃) :
    Units.map (g.map f₂₃).φ.toMonoidHom (rr Λ f₀₁ f₁₂ f₀₂) * rr Λ f₀₂ f₂₃ f₀₃ =
      rr Λ f₁₂ f₂₃ f₁₃ * rr Λ f₀₁ f₁₃ f₀₃ := by
  subst h₀₂ h₁₃
  have e : Units.map (g.map (f₁₂ ≫ f₂₃)).φ.toMonoidHom (Λ.w f₀₁) =
      Units.map (g.map f₂₃).φ.toMonoidHom (Units.map (g.map f₁₂).φ.toMonoidHom (Λ.w f₀₁)) := by
    rw [g.map_comp]; rfl
  unfold rr
  rw [e, map_mul, map_mul, map_inv]
  exact units_cancel _ _ _ _ _ _

theorem map_zK (Λ : CLiftK g D) (s : ℕ) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    (show (g.obj c).B from ((g ⋙ O (smFun X q)).map ρ).hom (zK Λ s σ)) =
      plogK (g.obj c).δ s (((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1) := by
  change (g.map ρ).φ (plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) = _
  rw [plogK_map (g.map ρ).dp s (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ), map_sub, map_one]
  rfl

theorem mem_J (Λ : CLiftK g D) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    ((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1 ∈ (g.obj c).J := by
  have := (g.map ρ).hle (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ)
  rw [Ideal.mem_comap, map_sub, map_one] at this
  exact this

theorem map_id_unit {c : C} (ρ : c ⟶ c) (h : ρ = 𝟙 c) (u : (g.obj c).Bˣ) :
    Units.map (g.map ρ).φ.toMonoidHom u = u := by
  subst h
  rw [g.map_id]
  ext; rfl

theorem nat_isUnit (T : Thick (smFun X q)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : T.B) := by
  have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn).isUnit
  have := h.map T.i
  rwa [map_natCast] at this

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  intro K _ _ X q C _ g D Λ s hs
  funext τ
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (toLast i τ)).hom (zK Λ s (face i τ)) = 0
  rw [Fin.sum_univ_four]
  have h0 := map_zK Λ s (face 0 τ) (toLast 0 τ)
  have h1 := map_zK Λ s (face 1 τ) (toLast 1 τ)
  have h2 := map_zK Λ s (face 2 τ) (toLast 2 τ)
  have h3 := map_zK Λ s (face 3 τ) (toLast 3 τ)
  have m0 := mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := plogK_four (g.obj (τ.obj (Fin.last 3))).δ s (hs _) (nat_isUnit (g.obj (τ.obj (Fin.last 3)))) m3 m1 m0 m2 hval
  have fin : ∀ a b c d : (g ⋙ O (smFun X q)).obj (τ.obj (Fin.last 3)), a + c = d + b →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro a b c d h
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    rw [e0, e1, e2, e3]
    have : (-1 : ℤ) ^ 3 = -1 := by norm_num
    rw [this, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul, neg_one_smul]
    calc a + -b + c + -d = (a + c) - (d + b) := by abel
      _ = 0 := by rw [h, sub_self]
  refine fin _ _ _ _ ?_
  exact add_eq (B := (g.obj (τ.obj (Fin.last 3))).B) h0 h2 h3 h1 p.symm

end GlobalTheory.CompanionTheory.ConeZcoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPerfectAdicRing
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ContFn

theorem smod_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    SModEq ((Ideal.span {a}) ^ n • ⊤ : Submodule R R) x y ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) {Γ : Type} [TopologicalSpace Γ]

theorem pi_nzd : A.pi ∈ nonZeroDivisors A.A := A.tf

theorem mem_contR_iff (f : Γ → A.A) :
    f ∈ A.contR Γ ↔ ∀ k : ℕ, ∀ γ : Γ, ∀ᶠ γ' in nhds γ, A.pi ^ k ∣ f γ' - f γ := by
  refine forall_congr' fun k => ?_
  change IsLocallyConstant (fun γ => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (f γ)) ↔ _
  rw [IsLocallyConstant.iff_eventually_eq]
  refine forall_congr' fun γ => Filter.eventually_congr (Filter.Eventually.of_forall fun γ' => ?_)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem pow_cancel {k j : ℕ} {a : A.A} (h : A.pi ^ (k + j) ∣ A.pi ^ k * a) : A.pi ^ j ∣ a := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hk : A.pi ^ k ∈ nonZeroDivisors A.A := pow_mem (pi_nzd A) k
  have := mem_nonZeroDivisors_iff_left.1 hk (a - A.pi ^ j * c) (by rw [mul_sub, hc, pow_add]; ring)
  exact sub_eq_zero.1 this

theorem frob_dvd {k : ℕ} {d : A.A} (h : A.pi ^ (l * k) ∣ A.frob d) : A.pi ^ k ∣ d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', rfl⟩ := A.frob_bijective.2 c
  refine ⟨c', A.frob_bijective.1 ?_⟩
  rw [hc, map_mul]
  congr 1
  change A.pi ^ (l * k) = (A.pi ^ k) ^ l
  rw [← pow_mul, mul_comm]

theorem val_pow_apply (f : A.contR Γ) (k : ℕ) (γ : Γ) : (f ^ k).1 γ = f.1 γ ^ k := by
  simp

theorem dvd_iff (k : ℕ) (f : A.contR Γ) : A.contC Γ A.pi ^ k ∣ f ↔ ∀ γ, A.pi ^ k ∣ f.1 γ := by
  constructor
  · rintro ⟨g, rfl⟩ γ
    refine ⟨g.1 γ, ?_⟩
    change (A.contC Γ A.pi ^ k).1 γ * g.1 γ = _
    rw [val_pow_apply]
    rfl
  · intro h
    choose g hg using h
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun j γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (k + j) γ] with γ' hγ'
      rw [hg γ', hg γ, ← mul_sub] at hγ'
      exact pow_cancel A hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    refine (hg γ).trans ?_
    change _ = (A.contC Γ A.pi ^ k).1 γ * g γ
    rw [val_pow_apply]
    rfl

theorem perfect : PerfectRing (A.contR Γ) l := by
  refine ⟨⟨fun x y h => ?_, fun f => ?_⟩⟩
  · refine Subtype.ext (funext fun γ => A.frob_bijective.1 ?_)
    have e := congrFun (congrArg Subtype.val h) γ
    change (x ^ l).1 γ = (y ^ l).1 γ at e
    rw [val_pow_apply, val_pow_apply] at e
    exact e
  · choose g hg using fun γ => A.frob_bijective.2 (f.1 γ)
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun k γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (l * k) γ] with γ' hγ'
      refine frob_dvd A ?_
      rw [map_sub, hg γ', hg γ]
      exact hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    change ((⟨g, hg'⟩ : A.contR Γ) ^ l).1 γ = _
    rw [val_pow_apply]
    exact hg γ

theorem complete : IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := by
  have hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have h1 : IsHausdorff (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun x hx => by
    refine Subtype.ext (funext fun γ => ?_)
    refine hc.toIsHausdorff.haus' (x.1 γ) fun n => (smod_iff _ _ _ _).2 ?_
    have := (dvd_iff A n x).1 (by simpa using (smod_iff _ _ _ _).1 (hx n)) γ
    simpa using this⟩
  have h2 : IsPrecomplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun f hf => by
    have hp : ∀ m n, m ≤ n → ∀ γ, A.pi ^ m ∣ (f m).1 γ - (f n).1 γ := fun m n h γ =>
      (dvd_iff A m (f m - f n)).1 ((smod_iff _ _ _ _).1 (hf h)) γ
    choose L hL using fun γ => hc.toIsPrecomplete.prec (f := fun n => (f n).1 γ)
      fun {m n} h => (smod_iff _ _ _ _).2 (hp m n h γ)
    have hL' : ∀ n γ, A.pi ^ n ∣ (f n).1 γ - L γ := fun n γ => (smod_iff _ _ _ _).1 (hL γ n)
    have hLm : L ∈ A.contR Γ := (mem_contR_iff A L).2 fun k γ => by
      filter_upwards [(mem_contR_iff A (f k).1).1 (f k).2 k γ] with γ' h
      have e : L γ' - L γ = ((f k).1 γ' - (f k).1 γ) - ((f k).1 γ' - L γ') + ((f k).1 γ - L γ) := by ring
      rw [e]
      exact dvd_add (dvd_sub h (hL' k γ')) (hL' k γ)
    exact ⟨⟨L, hLm⟩, fun n => (smod_iff _ _ _ _).2 ((dvd_iff A n _).2 fun γ => hL' n γ)⟩⟩
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

theorem contC_pi_nzd : A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) :=
  mem_nonZeroDivisors_iff_left.2 fun x hx => Subtype.ext (funext fun γ =>
    mem_nonZeroDivisors_iff_left.1 (pi_nzd A) (x.1 γ) (congrFun (congrArg Subtype.val hx) γ))

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ],
    PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧
      A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧
      ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔
        ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := fun A Γ _ =>
  ⟨perfect A, complete A, contC_pi_nzd A, fun k f => by
    simp only [Ideal.mem_span_singleton]
    exact dvd_iff A k f⟩

end GlobalTheory.CompanionTheory.ContFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicative
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.FilMul

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem factorial_mul_dpw (k : ℕ) :
    (k.factorial : WL l A.A) * dpw k A.xi = algebraMap A.W (WL l A.A) A.xi ^ k := by
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul]

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k :=
  Subtype.ext (by
    have h := factorial_mul_dpw A k
    simpa [PAlg.dxi0] using h)

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  show dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  have hi := A.isUnit_natCast i.factorial_ne_zero
  have hj := A.isUnit_natCast j.factorial_ne_zero
  have h : (((i + j).choose i : ℕ) : WL l A.A) * (i.factorial : WL l A.A) * (j.factorial : WL l A.A)
      = ((i + j).factorial : WL l A.A) := by
    rw [Nat.choose_symm_add, ← Nat.cast_mul, ← Nat.cast_mul,
      Nat.add_choose_mul_factorial_mul_factorial i j]
  apply hj.mul_left_cancel
  apply hi.mul_left_cancel
  calc (i.factorial : WL l A.A) * ((j.factorial : WL l A.A) * (dpw i A.xi * dpw j A.xi))
      = ((i.factorial : WL l A.A) * dpw i A.xi) * ((j.factorial : WL l A.A) * dpw j A.xi) := by ring
    _ = ((i + j).factorial : WL l A.A) * dpw (i + j) A.xi := by
        rw [factorial_mul_dpw, factorial_mul_dpw, factorial_mul_dpw, pow_add]
    _ = (i.factorial : WL l A.A) * ((j.factorial : WL l A.A)
          * ((((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi)) := by
        rw [← h]; ring

theorem Fil0_zero : A.Fil0 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, le_rfl, (divided_power_xi_zero A).symm⟩)

theorem Fil0_mul_le (r s : ℕ) : A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s) := by
  unfold PAlg.Fil0
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  show A.dxi0 i * A.dxi0 j ∈ Ideal.span _
  rw [divided_power_xi_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i + j, by omega, rfl⟩)

theorem Fil_eq_map (n r : ℕ) : A.Fil n r = (A.Fil0 r).map (A.mkAcr n) := by
  unfold PAlg.Fil PAlg.Fil0
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem PFil_eq_map (n : ℕ) : A.PFil n = A.PFil0.map (A.mkAcr n) := by
  rw [PAlg.PFil, PAlg.PFil0, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    Fil_eq_map]

theorem Fil_zero (n : ℕ) : A.Fil n 0 = ⊤ := by
  rw [Fil_eq_map, Fil0_zero, Ideal.map_top]

theorem Fil_mul_le (n r s : ℕ) : A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  rw [Fil_eq_map, Fil_eq_map, Fil_eq_map, ← Ideal.map_mul]
  exact Ideal.map_mono (Fil0_mul_le A r s)

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧
    (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧
    (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧
    (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧
    (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧
    (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧
    (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) :=
  fun A => ⟨Fil0_zero A, divided_power_xi_mul A, factorial_mul_divided_power_xi A, Fil0_mul_le A, Fil_eq_map A,
    PFil_eq_map A, Fil_zero A, Fil_mul_le A⟩

end GlobalTheory.CompanionTheory.FilMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSectionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_restrict_section : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  first | exact @GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | exact GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | (intros; apply GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq <;> assumption)
end

