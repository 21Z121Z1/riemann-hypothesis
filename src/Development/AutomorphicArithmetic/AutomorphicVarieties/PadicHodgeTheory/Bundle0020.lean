import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.GradedChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0016

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem hasWeight_of_generators {O R X Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) [AddCommGroup Q] [Module O Q] (D : R →ₗ[O] Q)
    (hD : D ∈ PtDer (W.origin h) Q) (j : X) (hz : ∀ s, W.wt s ≠ j → D (W.z s) = 0) : HasWt W.part j D := by
  classical
  let W' := WPres.free O W.wt
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  let D' : MvPowerSeries W.σ O →ₗ[O] Q := D ∘ₗ W.π.toLinearMap -
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries W.σ O →ₗ[O] O).smulRight (D (W.z s))
  have hD' : ∀ f, D' f = D (W.π f) - ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • D (W.z s) := fun f => by
    simp [D']
  have h0 := (der_extend O _ X W' h' Q).2 D' (fun f g => by
    have h1 : D (W.π f * W.π g) = W.origin h (W.π f) • D (W.π g) + W.origin h (W.π g) • D (W.π f) := hD _ _
    rw [hD', hD', hD', ho, ho, map_mul, h1, W.origin_π, W.origin_π]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
    abel) (fun (s : W.σ) => by
    show D' (MvPowerSeries.X s) = 0
    rw [hD']
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, WPres.z])
  rintro i hi _ ⟨f, hf, rfl⟩
  have h1 := hD' f
  rw [h0, LinearMap.zero_apply, eq_comm, sub_eq_zero] at h1
  refine h1.trans (Finset.sum_eq_zero fun s _ => ?_)
  by_cases hs : W.wt s = j
  · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
  · rw [hz s hs, smul_zero]

private theorem origin_eq {O R X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [AddCommGroup X] (W : WPres O X R) (x : R →ₐ[O] O)
    (hx : ∀ s, x (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = x := by
  have key : ∀ f, x (W.π f) = MvPowerSeries.constantCoeff f := by
    let F : MvPowerSeries W.σ O →ₐ[O] O :=
      { (MvPowerSeries.constantCoeff : MvPowerSeries W.σ O →+* O) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have := (co_ev O O O W.σ (AlgHom.id O O) 0 (fun _ => zero_mem _)).unique (y₁ := x.comp W.π) (y₂ := F)
      ⟨fun a => (x.comp W.π).commutes a, hx⟩ ⟨fun a => F.commutes a, fun s => MvPowerSeries.constantCoeff_X s⟩
    exact fun f => DFunLike.congr_fun this f
  refine ⟨fun f hf => by rw [← key, hf, map_zero], AlgHom.ext fun a => ?_⟩
  obtain ⟨f, rfl⟩ := W.surj a
  exact (W.origin_π _ f).trans (key f).symm

private theorem qcont_lin {l : ℕ} [Fact l.Prime] {V W X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace X] {φ : X → V} (hφ : QCont l φ) (ψ : V →ₗ[ℚ_[l]] W) :
    QCont l fun g => ψ (φ g) := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap ψ).comp hφ

private theorem qcont_add {l : ℕ} [Fact l.Prime] {V X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [TopologicalSpace X] {φ ψ : X → V} (hφ : QCont l φ) (hψ : QCont l ψ) : QCont l fun g => φ g + ψ g := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hφ hψ

private theorem qcont_dual {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    (f : X → DualNumber E) (h1 : QCont l fun x => (f x).fst) (h2 : QCont l fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  rw [e]
  exact qcont_add (qcont_lin h1 _) (qcont_lin h2 _)

theorem UpperTheory.V.Loc.liftChart :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (Q : ∀ (B : Type) [CommRing B] [Algebra O B], (Γ →* Matrix ι ι B) → Prop),
    (∀ (B B' : Type) [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B'] (f : B →ₐ[O] B') (r : Γ →* Matrix ι ι B), (Q B r → Q B' (mapRep (f : B →+* B') r)) ∧ (Function.Injective f → Q B' (mapRep (f : B →+* B') r) → Q B r)) →
    Represents (fun R' _ _ _ r => Q R' r.hom) ρ → ρ.TStable w →
    ∀ ρ₀ : Lift O rbar O, Q O ρ₀.hom → (∀ g a b, w a ≠ w b → ρ₀.hom g a b = 0) →
    (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : Γ →* Matrix ι ι B', mapRep (π' : B' →+* E) r' = mapRep (algebraMap O E) ρ₀.hom → (∀ a b, QCont l fun g => r' g a b) → Q B' r' → ∃ r : Γ →* Matrix ι ι B, (∀ a b, QCont l fun g => r g a b) ∧ Q B r ∧ mapRep (p : B →+* B') r = r') →
    ∃ (x : R →ₐ[O] O) (P : Ideal R) (n : ℕ) (u : Fin n → X) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), ρ.map x = ρ₀ ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ g a b, φ (ρ.hom g a b) ∈ wtPart E u (w a - w b)) ∧
      ∀ j, ∃ S : Submodule E (Γ → Matrix ι ι E), Nat.card {i // u i = j} = finrank E ↥S ∧ ∀ s, s ∈ S ↔ (∃ r' : Γ →* Matrix ι ι (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap O E (ρ₀.hom g a b), s g a b⟩) ∧ Q (DualNumber E) r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, w a - w b ≠ j → s g a b = 0 := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar X _ _ _ w E _ _ _ _ _ _ _ _ R _ _ _ ρ Q hQ hrep hst ρ₀ hQ0 hd hlift
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 _ ((hrep R').1 f')).unique h rfl
  have hQρ : Q R ρ.hom := (hrep R).1 (AlgHom.id O R)
  obtain ⟨x, hx, -⟩ := (hrep O).2 ρ₀ hQ0
  have hxe : ∀ g a b, x (ρ.hom g a b) = ρ₀.hom g a b := fun g a b => by rw [← hx]; rfl
  have hpt : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
      [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : Γ →* Matrix ι ι B),
      (∀ g a b, π (r g a b) = algebraMap O E (ρ₀.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → Q B r →
      ∃ f : R →ₐ[O] B, ∀ g a b, f (ρ.hom g a b) = r g a b := by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ r h1 h2 h3
    obtain ⟨C, hC, ρ', hρ'⟩ := exists_lift_factor_compact_subalgebra (l := l) rbar R ρ E B π hπ ((Algebra.ofId O E).comp x) r
      (fun g a b => by rw [h1, ← hxe]; rfl) h2
    have e : mapRep (C.val : C →+* B) ρ'.hom = r := MonoidHom.ext fun g => Matrix.ext fun a b => hρ' g a b
    obtain ⟨f, hf, -⟩ := (hrep C).2 ρ' ((hQ C B C.val ρ'.hom).2 Subtype.val_injective (e ▸ h3))
    refine ⟨C.val.comp f, fun g a b => ?_⟩
    rw [← hρ', ← hf]
    rfl
  have hc : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B) a b,
      QCont l fun g => f (ρ.hom g a b) := fun B _ _ _ _ _ _ _ f a b =>
    (ptCont (l := l) R B f).1 Γ _ (ρ.cont a b)
  obtain ⟨n, P, φ₀, hφ₀, -, ⟨y, hy, hyP⟩, -⟩ := smoothCompl (l := l) E R ⊥ x bot_le (by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc f' _ hf'
    obtain ⟨r, h1, h2, h3⟩ := hlift B π hπ B' π' hπ' p hp hpc (mapRep (f' : R →+* B') ρ.hom)
      (MonoidHom.ext fun g => Matrix.ext fun a b => (hf' _).trans (congrArg _ (hxe g a b)))
      (hc B' f') ((hQ R B' f' _).1 hQρ)
    have h4 : ∀ g a b, p (r g a b) = f' (ρ.hom g a b) := fun g a b =>
      congrFun (congrFun (DFunLike.congr_fun h3 g) a) b
    obtain ⟨f, hf⟩ := hpt B π hπ r (fun g a b => by rw [← hpc, AlgHom.comp_apply, h4, hf', hxe]) h1 h2
    have := homExt (l := l) rbar R ρ hgen B' ((p.restrictScalars O).comp f) f' fun g a b => by
      rw [← h4, ← hf]; rfl
    exact ⟨f, bot_le, fun a => DFunLike.congr_fun this a⟩)
  obtain ⟨W, hW, hWz⟩ := lift_grading O X Γ ι rbar w R ρ (fun g => ρ₀.hom g)
    (fun g a b => by rw [← ρ₀.red]; exact ((res O O).commutes _).symm) hd hgen hst
  obtain ⟨h, rfl⟩ := origin_eq W x fun s => by
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, map_sub, hxe, AlgHom.commutes]
    exact sub_self _
  obtain ⟨u, φ, hφ, hφw, hu⟩ := gradedChart (l := l) E R W h P φ₀ hφ₀ ⟨y, hy, hyP⟩
  refine ⟨_, P, n, u, φ, hx, hφ, ⟨y, hy, hyP⟩, fun g a b => hφw _ _ (hW g a b), fun j => ?_⟩
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  let ev : (R →ₗ[O] E) →ₗ[E] (Γ → Matrix ι ι E) :=
    { toFun := fun δ g => Matrix.of fun a b => δ (ρ.hom g a b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ δ g a b, ev δ g a b = δ (ρ.hom g a b) := fun _ _ _ _ => rfl
  have hder : ∀ D : R → E, (∃ D' ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, ⇑D' = D) ↔
      ∃ y : R →ₐ[O] DualNumber E, ∀ f, (y f).fst = algebraMap O E (W.origin h f) ∧ (y f).snd = D f := by
    letI : Module Oᵐᵒᵖ E := Module.compHom E (RingEquiv.toOpposite O).symm.toRingHom
    haveI : IsCentralScalar O E := ⟨fun _ _ => rfl⟩
    exact der_hom O R E E ((Algebra.ofId O E).comp (W.origin h))
  have hO : ∀ δ ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, δ ∈ PtDer (W.origin h) E := fun δ hδ f g => by
    rw [hδ f g]
    simp [Algebra.smul_def]
  have hz : ∀ δ ∈ PtDer (W.origin h) E, ∀ g a b c, δ (ρ.hom g a b - algebraMap O R c) = δ (ρ.hom g a b) := by
    intro δ hδ g a b c
    have h1 : δ (1 * 1) = W.origin h 1 • δ 1 + W.origin h 1 • δ 1 := hδ 1 1
    rw [mul_one, map_one (W.origin h), one_smul, left_eq_add] at h1
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero, sub_zero]
  refine ⟨(wtDer W.part (W.origin h) E j).map ev, (hu j).trans ?_, fun s => ⟨?_, ?_⟩⟩
  · classical
    rw [← Submodule.range_subtype (wtDer W.part (W.origin h) E j), ← LinearMap.range_comp, Submodule.range_subtype,
      LinearMap.finrank_range_of_inj]
    rw [injective_iff_map_eq_zero]
    intro δ hδ
    refine Subtype.ext ((der_extend O R X W h E).2 δ.1 (hO _ δ.2.1) fun s => ?_)
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, hz _ (hO _ δ.2.1)]
    exact congrFun (congrFun (congrFun hδ g) a) b
  · rintro ⟨δ, ⟨h1, h2⟩, rfl⟩
    obtain ⟨F, hF⟩ := (hder δ).1 ⟨δ, h1, rfl⟩
    refine ⟨⟨mapRep (F : R →+* DualNumber E) ρ.hom, fun g a b => TrivSqZeroExt.ext ?_ (hF _).2,
      (hQ R _ F _).1 hQρ⟩, fun a b => ?_, fun g a b hab => h2 _ hab _ (hW g a b)⟩
    · exact (hF _).1.trans (congrArg (algebraMap O E) (hxe g a b))
    · have := qcont_lin (hc (DualNumber E) F a b) (LinearMap.snd ℚ_[l] E E)
      simp only [hev, ← (hF _).2]
      exact this
  · rintro ⟨⟨r', h1, h2⟩, h3, h4⟩
    obtain ⟨F, hF⟩ := hpt (DualNumber E) (TrivSqZeroExt.fstHom E E E)
      (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
      r' (fun g a b => by rw [h1]; rfl) (fun a b => qcont_dual _ (by
        simp only [h1, ← hxe]
        exact hc E ((Algebra.ofId O E).comp (W.origin h)) a b) (by
        simp only [h1]
        exact h3 a b)) h2
    have hfst := homExt (l := l) rbar R ρ hgen E (((TrivSqZeroExt.fstHom E E E).restrictScalars O).comp F)
      ((Algebra.ofId O E).comp (W.origin h)) fun g a b => by
        show (F _).fst = algebraMap O E (W.origin h _)
        rw [hF, h1, hxe]
        rfl
    obtain ⟨δ, hδ, e⟩ := (hder fun f => (F f).snd).2 ⟨F, fun f => ⟨DFunLike.congr_fun hfst f, rfl⟩⟩
    have he : ∀ g a b, δ (ρ.hom g a b) = s g a b := fun g a b => by
      rw [e]
      show (F _).snd = _
      rw [hF, h1]
      rfl
    refine ⟨δ, ⟨hδ, hasWeight_of_generators W h δ (hO _ hδ) j fun t ht => ?_⟩, funext fun g => Matrix.ext (he g)⟩
    obtain ⟨g, a, b, e1, e2⟩ := hWz t
    rw [e1, hz _ (hO _ hδ), he, h4 g a b (e2 ▸ ht)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosBasic
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {E : Type} [Field E] [Algebra ℚ_[l] E]
  {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]

private noncomputable def spanT (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E]
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (W : Submodule E V) : Submodule E (V ⊗[ℚ_[l]] Bdr l) :=
  Submodule.span E {y | ∃ v ∈ W, ∃ b ∈ ((PP l).PD (botExt l)).Fil 0, y = v ⊗ₜ[ℚ_[l]] b}

private theorem filT_le_spanT : FilT (l := l) E V 0 ≤ spanT l (⊤ : Submodule E V) := by
  rintro _ ⟨z, rfl⟩
  induction z with
  | zero => simp
  | tmul v b => exact Submodule.subset_span ⟨v, trivial, b.1, b.2, by simp⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

private theorem spanT_le_filT (W : Submodule E V) : spanT l W ≤ FilT (l := l) E V 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, -, b, hb, rfl⟩
  exact ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

private theorem spanT_bot : spanT l (⊥ : Submodule E V) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨v, hv, b, -, rfl⟩
  rw [Submodule.mem_bot] at hv
  simp [hv]

private theorem map_spanT {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] E V'] (f : V →ₗ[E] V') (W : Submodule E V) (W' : Submodule E V')
    (hf : ∀ v ∈ W, f v ∈ W') (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W) :
    AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) y ∈ spanT l W' := by
  have : spanT l W ≤ (spanT l W').comap
      (AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, b, hb, rfl⟩
    exact Submodule.subset_span ⟨f v, hf v hv, b, hb, by simp⟩
  exact this hy

private theorem step (φ : G →* GQ l) (ρ : Representation E G V) (κ : G →* Eˣ)
    (hκ : FilD φ (chRep κ) 0 = ⊥) (W W' : Submodule E V) (x : V) (lam : V →ₗ[E] E)
    (hp : ∀ v ∈ W', v - lam v • x ∈ W)
    (heq : ∀ g, ∀ v ∈ W', lam (ρ g v) = (κ g : E) * lam v)
    (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W') (hD : y ∈ Ddr φ ρ) : y ∈ spanT l W := by
  set L := AlgebraTensorModule.map lam (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) with hL
  have hcomm : ∀ g, ∀ z ∈ spanT l W', L (actD φ ρ g z) = actD φ (chRep κ) g (L z) := by
    intro g z hz
    have : spanT l W' ≤ LinearMap.eqLocus (L ∘ₗ actD φ ρ g) (actD φ (chRep κ) g ∘ₗ L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, b, hb, rfl⟩
      simp [LinearMap.mem_eqLocus, hL, actD, chRep, heq g v hv]
    exact this hz
  have h0 : L y = 0 := by
    have : L y ∈ FilD φ (chRep κ) 0 := by
      refine ⟨?_, spanT_le_filT ⊤ (map_spanT lam W' ⊤ (fun _ _ => trivial) y hy)⟩
      simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hD ⊢
      intro g
      rw [← hcomm g y hy, hD g]
    rwa [hκ, Submodule.mem_bot] at this
  have h1 := map_spanT (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) W' W
    (fun v hv => by simpa using hp v hv) y hy
  have h2 : ∀ z : V ⊗[ℚ_[l]] Bdr l,
      AlgebraTensorModule.map (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) z =
      z - AlgebraTensorModule.map (LinearMap.toSpanSingleton E V x)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) (L z) := by
    intro z
    induction z with
    | zero => simp
    | tmul v b => simp [hL, sub_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  rwa [h2, h0, map_zero, sub_zero] at h1

private theorem H0_eq_bot_of_filD_zero_eq_bot (φ : G →* GQ l) (ρ : Representation E G V) [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (h : FilD φ ρ 0 = ⊥) : H0 ρ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hv
  haveI : Nontrivial (Bdr l) := nontrivial_of_ne 1 0 fun h1 =>
    ((PP l).PD (botExt l)).not_mem_filtration_two (by
      have : (((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t : Bdr l) = 0 := by
        rw [← mul_one (((PP l).PD (botExt l)).ι _), h1, mul_zero]
      rw [this]; exact zero_mem _)
  have hm : v ⊗ₜ[ℚ_[l]] (1 : Bdr l) ∈ FilD φ ρ 0 := by
    refine ⟨?_, v ⊗ₜ ⟨1, ((PP l).PD (botExt l)).one_mem⟩, by simp⟩
    simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    simp [actD, hv g]
  rw [h, Submodule.mem_bot] at hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ_[l] (one_ne_zero : (1 : Bdr l) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid ℚ_[l] V (TensorProduct.map LinearMap.id f z)) hm
  simpa [hf] using this

end SlopeTestRemainingChoices

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.posBasic :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0 ρ = ⊥ ∧ FilD φ ρ 0 = ⊥ ∧ Module.Finite E ↥(finiteCohomology φ ρ) ∧ finrank E ↥(finiteCohomology φ ρ) = φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  obtain ⟨hdr, n, F, hF0, hFn, hF⟩ := hpos
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have key : ∀ i ≤ n, (∀ g, ∀ v ∈ F i, ρ g v ∈ F i) ∧ ∀ y ∈ spanT l (F i), y ∈ Ddr φ ρ → y = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hF0, spanT_bot]
      refine ⟨fun g v hv => ?_, fun y hy _ => hy⟩
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i ih =>
      intro hi
      obtain ⟨hst, hz⟩ := ih (by omega)
      obtain ⟨hle, κ, ⟨w, hw, hκ⟩, x, hsup, hx⟩ := hF i (by omega)
      by_cases hxi : x ∈ F i
      · have : F (i + 1) = F i := by
          rw [hsup, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hxi
        rw [this]; exact ⟨hst, hz⟩
      obtain ⟨lam, hl1, hl0⟩ : ∃ lam : V →ₗ[E] E, lam x = 1 ∧ ∀ v ∈ F i, lam v = 0 := by
        have hne : (F i).mkQ x ≠ 0 := by simpa using hxi
        obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hne
        refine ⟨f ∘ₗ (F i).mkQ, hf, fun v hv => ?_⟩
        have : (F i).mkQ v = 0 := by simpa using hv
        rw [LinearMap.comp_apply, this, map_zero]
      have hdec : ∀ v ∈ F (i + 1), ∃ u ∈ F i, ∃ c : E, v = u + c • x := by
        intro v hv
        rw [hsup, Submodule.mem_sup] at hv
        obtain ⟨u, hu, z, hz, rfl⟩ := hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        exact ⟨u, hu, c, rfl⟩
      have hx1 : x ∈ F (i + 1) := by
        rw [hsup]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
      have hlx : ∀ g, lam (ρ g x) = (κ g : E) := by
        intro g
        have := hl0 _ (hx g)
        rwa [map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero] at this
      have hcont : Continuous (fun g => (κ g : E)) := by
        have h1 : Continuous (lam.restrictScalars ℚ_[l]) :=
          IsModuleTopology.continuous_of_linearMap _
        have h2 : Continuous (fun g => ρ g x) := hρ.comp (Continuous.prodMk_left x)
        have := h1.comp h2
        convert this using 1
        funext g
        exact (hlx g).symm
      have hfil := ((charFil φ hφ κ hcont w hκ).2 0).2 (by omega)
      refine ⟨fun g v hv => ?_, fun y hy hD => hz y (step φ ρ κ hfil (F i) (F (i + 1)) x lam ?_ ?_ y hy hD) hD⟩
      · obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        rw [map_add, map_smul]
        refine add_mem (hle (hst g u hu)) (Submodule.smul_mem _ _ ?_)
        have := add_mem (hle (hx g)) (Submodule.smul_mem _ (κ g : E) hx1)
        rwa [sub_add_cancel] at this
      · intro v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simpa [hl0 u hu, hl1] using hu
      · intro g v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simp [hl0 u hu, hl1, hl0 _ (hst g u hu), hlx, mul_comm]
  have hfil : FilD φ ρ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact (key n le_rfl).2 y (hFn ▸ filT_le_spanT hy.2) hy.1
  have hH0 := H0_eq_bot_of_filD_zero_eq_bot φ ρ hfil
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ ρ hρ hdr
  refine ⟨hH0, hfil, hfin, ?_⟩
  rw [hfil, hH0] at hdim
  simpa using hdim
end

