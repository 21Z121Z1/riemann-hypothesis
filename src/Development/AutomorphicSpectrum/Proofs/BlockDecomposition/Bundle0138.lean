import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCoord

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) :
        MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  letI := (strV q W).toAlgebra
  intro h
  haveI := hW.isLocalization_basicOpen g
  let φ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x :=
    fun x => φ.commutes x
  refine ⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩
  have h2 := RingHom.Etale.stableUnderComposition _ _ h
    (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)
  have e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) :
        MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) =
      (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp
        (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
          (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
      rw [strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]
      exact (hφ _).symm
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
      exact (hφ _).symm
  rw [e]
  exact h2

end GlobalTheory.CompanionTheory.GeoCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupProductRespectsHodgeFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CupdR

theorem dividedPowerFiltration_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r s : ℕ) :
    pdP δ r * pdP δ s ≤ pdP δ (r + s) := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    exacts [hl q h, hl' q h]
  · simp only [List.map_append, List.sum_append]
    omega
  · simp [List.map_append, List.prod_append]

theorem term_mem {b : Base} {L : b.Fun} {p n r : ℕ} (t : ComposableArrows (Thick L) n)
    (f : CH.Cn (CH.modF (thA L)) p) (hf : ∀ s, (show (s.obj (Fin.last p)).B from f s) ∈ (s.obj (Fin.last p)).pdPow r)
    (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    (show (t.obj (Fin.last n)).B from CH.term (CH.modF (thA L)) t f g hg) ∈ (t.obj (Fin.last n)).pdPow r :=
  dividedPowerFiltration_map (t.map (homOfLE (Fin.le_last (g (Fin.last p))))).dp r (hf (hg.functor ⋙ t))

theorem cup_bilinear_filtered {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (i j : ℕ) :
    (∃ b : HdR q i →ₗ[K] HdR q j →ₗ[K] HdR q (i + j), ∀ x y, b x y = cupK q rfl x y) ∧
    ∀ r s, ∀ x ∈ FilR q i r, ∀ y ∈ FilR q j s, cupK q rfl x y ∈ FilR q (i + j) (r + s) := by
  refine ⟨CrystallineSemistableComparison.P.cup_bilin (CH.mulP (thA (smFun X q))) (rfl : i + j = i + j), ?_⟩
  rintro r s x ⟨z, rfl, hz⟩ y ⟨w, rfl, hw⟩
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP (thA (smFun X q))) (rfl : i + j = i + j) z.1 w.1 z.2 w.2
  refine ⟨⟨_, hc⟩, e.symm, fun t => ?_⟩
  exact dividedPowerFiltration_mul _ r s (Ideal.mul_mem_mul
    (term_mem t z.1 hz (CH.front rfl) (CH.front_mono rfl)) (term_mem t w.1 hw (CH.back rfl) (CH.back_mono rfl)))

end GlobalTheory.CompanionTheory.CupdR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.D2Apply
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfExt

section Gen

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Ext {N Q : Type} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R' Q] (c : N → Q) : Prop :=
  ∃ e : R' ⊗[R] N ≃ₗ[R'] Q, ∀ b, e (1 ⊗ₜ b) = c b

variable {R R'}

theorem Ext.pi {J : Type} [Finite J] {N Q : J → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module R' (Q i)] (c : ∀ i, N i → Q i) (h : ∀ i, Ext R R' (c i)) :
    Ext R R' (fun (f : ∀ i, N i) i ↦ c i (f i)) := by
  classical
  have := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' N).trans (LinearEquiv.piCongrRight e), fun b ↦ funext fun i ↦ ?_⟩
  simp [he]

variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]

variable (M) in

def tw (E : R' ⊗[R] N ≃ₗ[R'] Q) : M ⊗[R] N ≃+ M ⊗[R'] Q :=
  ((AlgebraTensorModule.cancelBaseChange R R' R' M N).symm.trans (LinearEquiv.lTensor M E)).toAddEquiv

theorem tw_tmul (E : R' ⊗[R] N ≃ₗ[R'] Q) (x : M) (n : N) : tw M E (x ⊗ₜ n) = x ⊗ₜ E (1 ⊗ₜ n) := by
  simp [tw]

theorem tw_nat (E : R' ⊗[R] N ≃ₗ[R'] Q) (E₂ : R' ⊗[R] N₂ ≃ₗ[R'] Q₂) (g : N →ₗ[R] N₂) (h : Q →ₗ[R'] Q₂)
    (H : ∀ n, h (E (1 ⊗ₜ n)) = E₂ (1 ⊗ₜ g n)) (t : M ⊗[R] N) :
    tw M E₂ (g.lTensor M t) = h.lTensor M (tw M E t) := by
  induction t with
  | zero => simp
  | tmul x n => simp [tw_tmul, H]
  | add a b ha hb => simp only [map_add, ha, hb]

end Gen

theorem QIsoAt.transport {R R' A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing R']
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R' A₀'] [Module R' A₁'] [Module R' A₂'] [Module R' B₀'] [Module R' B₁'] [Module R' B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R'] A₁'} {a₁' : A₁' →ₗ[R'] A₂'} {b₀' : B₀' →ₗ[R'] B₁'} {b₁' : B₁' →ₗ[R'] B₂'} {f' : A₁' →ₗ[R'] B₁'}
    (u₁ : A₁ ≃+ A₁') (u₂ : A₂ ≃+ A₂') (v₁ : B₁ ≃+ B₁') (v₂ : B₂ ≃+ B₂')
    (h₁ : ∀ x, u₂ (a₁ x) = a₁' (u₁ x)) (h₂ : ∀ z, v₂ (b₁ z) = b₁' (v₁ z)) (hf : ∀ x, v₁ (f x) = f' (u₁ x))
    (ha : ∀ y, ∃ y', a₀' y' = u₁ (a₀ y)) (hb : ∀ y, ∃ y', b₀' y' = v₁ (b₀ y)) (hb' : ∀ y', ∃ y, v₁ (b₀ y) = b₀' y')
    (q : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  obtain ⟨q₁, q₂⟩ := q
  refine ⟨fun x' hx ⟨y', hy⟩ ↦ ?_, fun z' hz ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := u₁.surjective x'
    obtain ⟨y, hy'⟩ := hb' y'
    obtain ⟨w, hw⟩ := q₁ x (u₂.injective (by rw [h₁, hx, map_zero]))
      ⟨y, v₁.injective (by rw [hy', hy, hf])⟩
    obtain ⟨w', hw'⟩ := ha w
    exact ⟨w', by rw [hw', hw]⟩
  · obtain ⟨z, rfl⟩ := v₁.surjective z'
    obtain ⟨x, y, hx, hy⟩ := q₂ z (v₂.injective (by rw [h₂, hz, map_zero]))
    obtain ⟨y', hy'⟩ := hb y
    exact ⟨u₁ x, y', by rw [← h₁, hx, map_zero], by rw [hy', ← hy, map_sub, hf]⟩

section Main

theorem bc_ext {R R' N Q : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R' Q] (g h : R' ⊗[R] N →ₗ[R'] Q) (H : ∀ n, g (1 ⊗ₜ n) = h (1 ⊗ₜ n)) : g = h := by
  refine LinearMap.ext fun t ↦ ?_
  induction t with
  | zero => simp
  | tmul r n =>
    have e : r ⊗ₜ[R] n = r • ((1 : R') ⊗ₜ[R] n) := by simp [TensorProduct.smul_tmul']
    rw [e, map_smul, map_smul, H]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem d2_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (z : C2 F)
    {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem ext0 (m : BC F F') : Ext R R' (fun (f : C0 F) T ↦ m.α T (f T) : C0 F → C0 F') :=
  Ext.pi (fun T b ↦ m.α T b) fun T ↦ m.bij T

theorem ext1 (m : BC F F') : Ext R R' (fun (f : C1 F) T T' φ ↦ m.α T' (f T T' φ) : C1 F → C1 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T')
    (fun T (g : ∀ (T' : C) (_ : T ⟶ T'), F.obj T') T' φ ↦ m.α T' (g T' φ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (_ : T ⟶ T'), F'.obj T')
    (fun T' (g : ∀ (_ : T ⟶ T'), F.obj T') φ ↦ m.α T' (g φ)) fun T' ↦
  Ext.pi (fun _ b ↦ m.α T' b) fun _ ↦ m.bij T'

theorem ext2 (m : BC F F') :
    Ext R R' (fun (f : C2 F) T T' T'' φ ψ ↦ m.α T'' (f T T' T'' φ ψ) : C2 F → C2 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T (g : ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T' T'' φ ψ ↦
      m.α T'' (g T' T'' φ ψ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T' (g : ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T'' φ ψ ↦
      m.α T'' (g T'' φ ψ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T'' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') φ ψ ↦ m.α T'' (g φ ψ)) fun T'' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T''), F'.obj T'')
    (fun φ (g : ∀ (_ : T' ⟶ T''), F.obj T'') ψ ↦ m.α T'' (g ψ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T'' b) fun _ ↦ m.bij T''

theorem ext3 (m : BC F F') :
    Ext R R' (fun (f : C3 F) T T' T'' T''' φ ψ χ ↦ m.α T''' (f T T' T'' T''' φ ψ χ) : C3 F → C3 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T (g : ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T' T'' T''' φ ψ χ ↦ m.α T''' (g T' T'' T''' φ ψ χ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T' (g : ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T'' T''' φ ψ χ ↦ m.α T''' (g T'' T''' φ ψ χ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T'' (g : ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T''' φ ψ χ ↦ m.α T''' (g T''' φ ψ χ)) fun T'' ↦
  Ext.pi (Q := fun T''' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T''' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') φ ψ χ ↦
      m.α T''' (g φ ψ χ)) fun T''' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun φ (g : ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') ψ χ ↦ m.α T''' (g ψ χ)) fun _ ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T'' ⟶ T'''), F'.obj T''')
    (fun ψ (g : ∀ (_ : T'' ⟶ T'''), F.obj T''') χ ↦ m.α T''' (g χ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T''' b) fun _ ↦ m.bij T'''

theorem perf_ext (m : BC F F') (h : Perf F) : Perf F' := by
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f₀, p₀⟩, ⟨f₁, p₁⟩, ⟨f₂, p₂⟩, ⟨f₃, p₃⟩, h₁₀, h₂₁, s₀, s₁,
    ⟨ψ₃, s₂⟩, hM⟩ := h
  obtain ⟨E₀, e₀⟩ := ext0 m
  obtain ⟨E₁, e₁⟩ := ext1 m
  obtain ⟨E₂, e₂⟩ := ext2 m
  obtain ⟨E₃, e₃⟩ := ext3 m
  have t₀ : ∀ x, d0 F' (E₀ (1 ⊗ₜ x)) = E₁ (1 ⊗ₜ d0 F x) := fun x ↦ by
    rw [e₀, e₁]
    funext T T' φ
    simp only [amitsur_d0_apply, map_sub, m.naturality]
  have t₁ : ∀ x, d1 F' (E₁ (1 ⊗ₜ x)) = E₂ (1 ⊗ₜ d1 F x) := fun x ↦ by
    rw [e₁, e₂]
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add, m.naturality]
  have t₂ : ∀ x, d2 F' (E₂ (1 ⊗ₜ x)) = E₃ (1 ⊗ₜ d2 F x) := fun x ↦ by
    rw [e₂, e₃]
    funext T T' T'' T''' φ ψ χ
    simp only [d2_apply, map_sub, map_add, m.naturality]
  refine ⟨.of R' (R' ⊗[R] P₀), .of R' (R' ⊗[R] P₁), .of R' (R' ⊗[R] P₂), .of R' (R' ⊗[R] P₃),
    a₀.baseChange R', a₁.baseChange R', a₂.baseChange R',
    E₀.toLinearMap ∘ₗ ψ₀.baseChange R', E₁.toLinearMap ∘ₗ ψ₁.baseChange R', E₂.toLinearMap ∘ₗ ψ₂.baseChange R',
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₀)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₀))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₁)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₁))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₂)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₂))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₃)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₃))⟩,
    ?_, ?_, ?_, ?_, ⟨E₃.toLinearMap ∘ₗ ψ₃.baseChange R', ?_⟩, fun M ↦ ?_⟩
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₁₀ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₂₁ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₀ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₀]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₁ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₁]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₂ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₂]
  · letI : Module R M := Module.compHom M (algebraMap R R')
    haveI : IsScalarTower R R' M := ⟨fun r s x ↦ by
      change (r • s) • x = (algebraMap R R' r) • (s • x)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨q₀, q₁, q₂⟩ := hM (ModuleCat.of R M)
    let r₀ : R' ⊗[R] P₀ ≃ₗ[R'] R' ⊗[R] P₀ := .refl _ _
    let r₁ : R' ⊗[R] P₁ ≃ₗ[R'] R' ⊗[R] P₁ := .refl _ _
    let r₂ : R' ⊗[R] P₂ ≃ₗ[R'] R' ⊗[R] P₂ := .refl _ _
    let r₃ : R' ⊗[R] P₃ ≃ₗ[R'] R' ⊗[R] P₃ := .refl _ _
    have nA₀ : ∀ t, tw M r₁ (a₀.lTensor M t) = (a₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ r₁ a₀ _ fun n ↦ by simp [r₀, r₁, LinearMap.baseChange_tmul]
    have nA₁ : ∀ t, tw M r₂ (a₁.lTensor M t) = (a₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ r₂ a₁ _ fun n ↦ by simp [r₁, r₂, LinearMap.baseChange_tmul]
    have nA₂ : ∀ t, tw M r₃ (a₂.lTensor M t) = (a₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ r₃ a₂ _ fun n ↦ by simp [r₂, r₃, LinearMap.baseChange_tmul]
    have nD₀ : ∀ t, tw M E₁ ((d0 F).lTensor M t) = (d0 F').lTensor M (tw M E₀ t) := tw_nat E₀ E₁ _ _ t₀
    have nD₁ : ∀ t, tw M E₂ ((d1 F).lTensor M t) = (d1 F').lTensor M (tw M E₁ t) := tw_nat E₁ E₂ _ _ t₁
    have nD₂ : ∀ t, tw M E₃ ((d2 F).lTensor M t) = (d2 F').lTensor M (tw M E₂ t) := tw_nat E₂ E₃ _ _ t₂
    have nP₀ : ∀ t, tw M E₀ (ψ₀.lTensor M t) =
        (E₀.toLinearMap ∘ₗ ψ₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ E₀ ψ₀ _ fun n ↦ by simp [r₀, LinearMap.baseChange_tmul]
    have nP₁ : ∀ t, tw M E₁ (ψ₁.lTensor M t) =
        (E₁.toLinearMap ∘ₗ ψ₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ E₁ ψ₁ _ fun n ↦ by simp [r₁, LinearMap.baseChange_tmul]
    have nP₂ : ∀ t, tw M E₂ (ψ₂.lTensor M t) =
        (E₂.toLinearMap ∘ₗ ψ₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ E₂ ψ₂ _ fun n ↦ by simp [r₂, LinearMap.baseChange_tmul]
    exact ⟨QIsoAt.transport (tw M r₀) (tw M r₁) (tw M E₀) (tw M E₁) nA₀ nD₀ nP₀
        (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) q₀,
      QIsoAt.transport (tw M r₁) (tw M r₂) (tw M E₁) (tw M E₂) nA₁ nD₁ nP₁
        (fun y ↦ ⟨tw M r₀ y, (nA₀ y).symm⟩) (fun y ↦ ⟨tw M E₀ y, (nD₀ y).symm⟩)
        (fun y ↦ ⟨(tw M E₀).symm y, by rw [nD₀, AddEquiv.apply_symm_apply]⟩) q₁,
      QIsoAt.transport (tw M r₂) (tw M r₃) (tw M E₂) (tw M E₃) nA₂ nD₂ nP₂
        (fun y ↦ ⟨tw M r₁ y, (nA₁ y).symm⟩) (fun y ↦ ⟨tw M E₁ y, (nD₁ y).symm⟩)
        (fun y ↦ ⟨(tw M E₁).symm y, by rw [nD₁, AddEquiv.apply_symm_apply]⟩) q₂⟩

end Main

theorem main : PerfBaseSt := by
  intro R _ P _ _ F h R' _ _ F' m
  haveI : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  exact perf_ext m h

end GlobalTheory.CompanionTheory.PerfExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeCx

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]

section Act

variable (F : C ⥤ CommAlgCat.{0} R)

def act {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : Cn F m →ₗ[R] Cn F n :=
  LinearMap.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).toLinearMap ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem act_apply {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : Cn F m) (c : Fin (n + 1) ⥤ C) :
    act F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) :=
  rfl

private theorem mp_map_endo_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x : Fin (n + 1)} (h : x ⟶ x)
    (b : F.obj (c.obj x)) : GlobalTheory.CatCoh.mp F (c.map h) b = b := by
  have hc : c.map h = 𝟙 (c.obj x) := by
    rw [Subsingleton.elim h (𝟙 x)]
    exact c.map_id x
  rw [hc, GlobalTheory.CatCoh.mp_id]

private theorem mp_map_comp_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)}
    (h : x ⟶ z) (h₁ : x ⟶ y) (h₂ : y ⟶ z) (b : F.obj (c.obj x)) :
    GlobalTheory.CatCoh.mp F (c.map h) b =
      GlobalTheory.CatCoh.mp F (c.map h₂) (GlobalTheory.CatCoh.mp F (c.map h₁) b) := by
  rw [Subsingleton.elim h (h₁ ≫ h₂), Functor.map_comp, GlobalTheory.CatCoh.mp_comp]

theorem act_id {n : ℕ} (f : Cn F n) : act F (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) f = f := by
  funext c
  show GlobalTheory.CatCoh.mp F (c.map (𝟙 (Fin.last n))) (f c) = f c
  exact mp_map_endo_apply F c _ _

theorem act_comp {k m n : ℕ} (θ : Fin (k + 1) →o Fin (m + 1)) (ψ : Fin (m + 1) →o Fin (n + 1))
    (f : Cn F k) : act F (ψ.comp θ) f = act F ψ (act F θ f) := by
  funext c
  exact mp_map_comp_apply F c _
    (homOfLE (ψ.monotone (Fin.le_last (θ (Fin.last k))))) (homOfLE (Fin.le_last (ψ (Fin.last m))))
    (f ((ψ.comp θ).monotone.functor ⋙ c))

def cosimp : CosimplicialObject (ModuleCat.{0} R) where
  obj a := ModuleCat.of R (Cn F a.len)
  map θ := ModuleCat.ofHom (act F θ.toOrderHom)
  map_id a := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_id F f)
  map_comp θ ψ := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_comp F θ.toOrderHom ψ.toOrderHom f)

theorem cof_eq (n : ℕ) (i : Fin (n + 2)) :
    cof F n i = act F (Fin.succAboveOrderEmb i).toOrderHom := rfl

theorem objD_hom (n : ℕ) : (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp F) n).hom = dn F n := by
  unfold AlgebraicTopology.AlternatingCofaceMapComplex.objD
  rw [ModuleCat.hom_sum, MainStatements.Hodge.dn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModuleCat.hom_zsmul]
  first
  | rfl
  | (rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]; rfl)

theorem dn_comp_dn (n : ℕ) : dn F (n + 1) ∘ₗ dn F n = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (GlobalTheory.CompanionTheory.HodgeCx.cosimp F) n)
  rw [ModuleCat.hom_comp, GlobalTheory.CompanionTheory.HodgeCx.objD_hom, GlobalTheory.CompanionTheory.HodgeCx.objD_hom,
    ModuleCat.hom_zero] at h
  exact h

end Act

theorem pulln_cof {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) (i : Fin (n + 2)) (f : Cn F n) :
    pulln m (n + 1) (cof F n i f) = cof G n i (pulln m n f) := by
  funext c
  exact m.3 (c.map (homOfLE (Fin.le_last _))) (f (MainStatements.Hodge.face i c ⋙ m.1))

theorem pulln_dn {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) :
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, MainStatements.Hodge.dn, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, map_zsmul, GlobalTheory.CompanionTheory.HodgeCx.pulln_cof]

theorem cxSt : CxSt := by
  intro R _ C _ F
  exact ⟨GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F, fun D _ G m n => GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n⟩

end GlobalTheory.CompanionTheory.HodgeCx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquivStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exP_of_compatible_equiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_derivations_of_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra; ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | exact GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | (intros; apply GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalChartAtPrime
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotChart

theorem exists_smooth_chart :
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  intro R _ X s e g _hes hsm p
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ :=
    hsm.exists_isStandardSmoothOfRelativeDimension (e (show Sp R from p))
  have hopen : IsOpen (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) :=
    (e ⁻¹ᵁ V).isOpen
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (show p ∈ (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) from hxV) hopen
  have hr : r ∉ p.asIdeal := hpr
  have hrange0 : Set.range (spMap (algebraMap R (Localization.Away r))) =
      ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  have hnt : Nontrivial (Localization.Away r) := by
    have hp : p ∈ Set.range (spMap (algebraMap R (Localization.Away r))) := by
      rw [hrange0]; exact hpr
    obtain ⟨q, -⟩ := hp
    exact (PrimeSpectrum.nonempty_iff_nontrivial).1 ⟨q⟩
  have hrange : Set.range (spMap (algebraMap R (Localization.Away r)) ≫ e) ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap (algebraMap R (Localization.Away r))) y ∈
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← hrange0]; exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hrV hy
  let l : Sp (Localization.Away r) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift hV.fromSpec (spMap (algebraMap R (Localization.Away r)) ≫ e) hrange
  have hl : l ≫ hV.fromSpec = spMap (algebraMap R (Localization.Away r)) ≫ e :=
    IsOpenImmersion.lift_fac _ _ hrange
  let ε : Γ(X, V) ⟶ CommRingCat.of (Localization.Away r) := Spec.preimage l
  have hε : Spec.map ε = l := Spec.map_preimage l
  let φ : Γ(Sp R, U) ⟶ Γ(X, V) := s.appLE U V hVU
  letI aCA : Algebra Γ(Sp R, U) Γ(X, V) := φ.hom.toAlgebra
  letI aAL : Algebra Γ(X, V) (Localization.Away r) := ε.hom.toAlgebra
  have hA : Nontrivial Γ(X, V) := ε.hom.domain_nontrivial
  have hS : Algebra.IsStandardSmoothOfRelativeDimension g Γ(Sp R, U) Γ(X, V) := hstd
  have hS' : Algebra.IsStandardSmooth Γ(Sp R, U) Γ(X, V) := hS.isStandardSmooth
  refine ⟨r, Γ(X, V), Γ(Sp R, U), inferInstance, inferInstance, aCA, aAL, hV.fromSpec, hU.fromSpec,
    hr, inferInstance, inferInstance, ?_, ?_, inferInstance, inferInstance, ?_⟩
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec s hU hV hVU).symm
  · rw [← hl, ← hε]; rfl
  · exact Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g)

end GlobalTheory.CompanionTheory.CotChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_representation_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
end

