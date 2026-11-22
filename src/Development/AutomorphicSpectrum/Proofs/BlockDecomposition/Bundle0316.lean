import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FirstChernPullback

theorem mem_VD_pb {X X' : Scheme.{0}} (D : E.LineData X) (u : X' ⟶ X) {V : X.Opens} (hV : V ∈ 𝒱D D) :
    u ⁻¹ᵁ V ∈ 𝒱D (D.pb u) := by
  obtain ⟨σ, hσ⟩ := hV
  refine ⟨Limits.pullback.lift ((u ∣_ V) ≫ σ) (u ⁻¹ᵁ V).ι ?_, ?_⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact Limits.pullback.lift_snd _ _ _

theorem sSup_preimage {X X' : Scheme.{0}} (𝒲 : Set X.Opens) (u : X' ⟶ X) (h : sSup 𝒲 = ⊤) :
    sSup ((fun V : X.Opens => u ⁻¹ᵁ V) '' 𝒲) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : u x ∈ sSup 𝒲 := by rw [h]; trivial
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  exact TopologicalSpace.Opens.mem_sSup.2 ⟨_, ⟨V, hV, rfl⟩, hxV⟩

theorem u_congr {X : Scheme.{0}} (D : E.LineData X) {A : CommRingCat.{0}} {a a' b b' : Spec A ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso A).hom.hom (D.u a b h) = (Scheme.ΓSpecIso A).hom.hom (D.u a' b' h') := by
  subst ea eb
  rfl

end GlobalTheory.CompanionTheory.FirstChernPullback

open GlobalTheory.CompanionTheory.FirstChernPullback in

theorem GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := by
  intro O O' R R' _ _ _ _ I I' γ γ' X X' q q' κ κ' σ m p Q Q₀ hQ h D N z z' hD hz hz'
  let 𝒱 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D
  have h1 : St Q₀ 𝒱 ≤ St Q₀ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X'.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    exact (sSup_preimage _ m.u hD).ge
  apply (GlobalTheory.T.cech_refinement_cohomology_bijective Q₀ hQ 𝒱 {⊤} h1 hc 2).2.2.1
  let G' : (St Q₀ 𝒱).FullSubcategory ⥤ (St Q₀ {⊤}).FullSubcategory := ObjectProperty.ιOfLE h1
  let sm := m.smor Q (St Q₀ {⊤}) h
  let G'' : (St Q₀ 𝒱).FullSubcategory ⥤ Q.FullSubcategory := G' ⋙ sm.G
  have hV' : ∀ T, ∃ V ∈ 𝒱D (D.pb m.u), InU V (G'.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨_, mem_VD_pb D m.u hV, hT⟩
  have hV : ∀ T, ∃ V ∈ 𝒱D D, InU V (G''.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨V, hV, hT⟩
  obtain ⟨Λ'⟩ := GlobalTheory.T.exists_crystalline_lift (q := q') (b := nlBase R' I' γ' p) (ht := rfl) (κ := κ') (G' ⋙ (St Q₀ {⊤}).ι) (D.pb m.u) (fun T => by
    obtain ⟨V, ⟨s, hs⟩, hT⟩ := hV' T
    have hr : Set.range (pt (G'.obj T).obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hT (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (G'.obj T).obj) hr ≫ s, ?_⟩
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
    rfl)
  let Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G'' ⋙ Q.ι) D :=
    { p := fun T => Λ'.p T ≫ Limits.pullback.fst D.f m.u
      hp := fun T => by
        have e := Λ'.hp T
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ m.u) e
      w := fun φ => Λ'.w φ
      hw := fun {T T'} φ hh => by
        have hh' : (B.thSp ((G' ⋙ (St Q₀ {⊤}).ι).map φ) ≫ Λ'.p T) ≫ (D.pb m.u).f = Λ'.p T' ≫ (D.pb m.u).f := by
          rw [Category.assoc, Λ'.hp T, Λ'.hp T']
          exact congrArg (fun y => y.1.2) ((G' ⋙ (St Q₀ {⊤}).ι).map φ).pt
        refine (Λ'.hw φ hh').trans ?_
        exact u_congr D (Category.assoc _ _ _) rfl _ hh }
  obtain ⟨hz1, hcl1⟩ := hz' _ G' hV' Λ'
  obtain ⟨hz2, hcl2⟩ := hz _ G'' hV Λ
  let ψ : CH.Mor (G' ⋙ CH.modF (sP (St Q₀ {⊤})).A) (CH.modF (sP (St Q₀ 𝒱)).A) (RingHom.id R') :=
    { G := 𝟭 _, τ := fun T => (incl h1).o.τ T, nat := fun φ x => (incl h1).o.nat φ x }
  let μ : CH.Mor (G'' ⋙ CH.modF (sP Q).A) (CH.modF (sP (St Q₀ 𝒱)).A) σ :=
    { G := 𝟭 _, τ := fun T => sm.o.τ (G'.obj T), nat := fun φ x => sm.o.nat (G'.map φ) x }
  have e1 : (incl h1).o.pull 2 z' = ψ.pull 2 ((CH.Mor.restrict (CH.modF (sP (St Q₀ {⊤})).A) G').pull 2 z') := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rfl
  have e2 : (incl h1).o.pull 2 (sm.o.pull 2 z) = μ.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) G'').pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hE : μ.pullC 2 (Λ.coc (RingHom.id R) N) = ψ.pullC 2 (Λ'.coc (RingHom.id R') N) := by
    funext s
    rfl
  have b1 : CH.d _ 2 (ψ.pullC 2 (Λ'.coc (RingHom.id R') N)) = 0 := by
    rw [ψ.d_pullC, hz1, map_zero]
  have b2 : CH.d _ 2 (μ.pullC 2 (Λ.coc (RingHom.id R) N)) = 0 := by
    rw [μ.d_pullC, hz2, map_zero]
  have k1 : ψ.pull 2 ((CH.cx _).cls _ hz1) = (CH.cx _).cls _ b1 := CrystallineSemistableComparison.P.mapH_cls ψ.hom 2 _ hz1 b1
  have k2 : μ.pull 2 ((CH.cx _).cls _ hz2) = (CH.cx _).cls _ b2 := CrystallineSemistableComparison.P.mapH_cls μ.hom 2 _ hz2 b2
  have key : ∀ (a b : CH.Cn (CH.modF (sP (St Q₀ 𝒱)).A) 2) (ha : CH.d _ 2 a = 0) (hb : CH.d _ 2 b = 0), a = b →
      (CH.cx _).cls a ha = (CH.cx _).cls b hb := by
    rintro a _ ha hb rfl
    rfl
  rw [e1, e2, ← hcl1, ← hcl2, k1, k2]
  exact key _ _ b2 b1 hE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

theorem map_mem_sub_of_mul {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (g : B →+* B) (s : W → W) (hs : ∀ w, g (f w) = f (s w)) (u : W) (hu : s ξ = u * ξ) :
    ∀ x ∈ sub f ξ l M, g x ∈ sub f ξ l M := by
  have hle : sub f ξ l M ≤ (sub f ξ l M).comap g := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · show g (f w) ∈ sub f ξ l M
      rw [hs]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · show g (dpE f ξ l M i) ∈ sub f ξ l M
      have hη : g (η f ξ l M) = f u * η f ξ l M := by
        rw [η, map_rat_smul, hs, hu, map_mul, mul_smul_comm]
      have hd : g (dpE f ξ l M i) = f u ^ i * dpE f ξ l M i := by
        rw [dpE, map_rat_smul, map_pow, hη, mul_pow, mul_smul_comm]
      rw [hd]
      have h1 : f u ∈ sub f ξ l M := Subring.subset_closure (Or.inl ⟨u, rfl⟩)
      have h2 : dpE f ξ l M i ∈ sub f ξ l M := Subring.subset_closure (Or.inr ⟨i, rfl⟩)
      exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem h1 i) h2
  exact fun x hx => hle hx

theorem gal_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ)
    (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)),
    ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M,
      Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K M k g hT
  have hmem : toBot g.1 • xi0 l ∈ RingHom.ker (theta0 l) :=
    gal_smul_mem_ker_fontaineTheta (toBot g.1) (by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta0, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine map_mem_sub_of_mul (fk l k) (xi0 l) l M _ (fun w => toBot g.1 • w) (fun w => ?_) u hu.symm
  show Ideal.quotientMap _ (gP l g) hT (Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l w)) =
    Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l (toBot g.1 • w))
  rw [Ideal.quotientMap_mk, ← gal_smul_wittToBDeRhamPlus]
  rfl

end GlobalTheory.CompanionTheory.LatGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
section
set_option autoImplicit false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

private theorem galBdRHom_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : BDeRhamPlus (normInteger ℂ_[p]) p)
    (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)) :
    galBdRHom σ x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have h1 : galBdRHom σ⁻¹ (galBdRHom σ x) = x := by
    rw [← RingHom.comp_apply, ← galBdRHom_mul, inv_mul_cancel, galBdRHom_one, RingHom.id_apply]
  rw [← h1]
  exact hu.map _

theorem span_tBdR_pow_le_comap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (k : ℕ) (g : K.fixingSubgroup) :
    Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  have ht : Lat.gP l g (tBdR l) ∈ Ideal.span {tBdR l} := by
    rw [← maximalIdeal_eq_span_tBdR]
    exact galBdRHom_mem_maximalIdeal _ _ (by rw [maximalIdeal_eq_span_tBdR]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hc, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.LatGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
section
open MeasureTheory Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.GLUnimod

variable {n : ℕ}

noncomputable def dg (d : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := diagonal fun i => (d i : ℂ)
  inv := diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by simp [diagonal_mul_diagonal, diagonal_one]
  inv_val := by simp [diagonal_mul_diagonal, diagonal_one]

theorem dg_mul (d e : Fin n → ℂˣ) : dg (d * e) = dg d * dg e := by
  apply Units.ext
  simp [dg, diagonal_mul_diagonal]

theorem dg_one : dg (1 : Fin n → ℂˣ) = 1 := by
  apply Units.ext
  simp [dg, diagonal_one]

noncomputable def pm (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]
  inv_val := by rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]

theorem pm_mul_dg (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂˣ) :
    pm σ * dg d = dg (d ∘ σ) * pm σ := by
  ext1
  ext i j
  simp only [pm, dg, Units.val_mul, mul_diagonal, diagonal_mul, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · subst h
    ring
  · ring

noncomputable def tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) : GL (Fin n) ℂ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [transvection_mul_transvection_same _ _ hij]; simp

theorem tv_mul {i j : Fin n} (hij : i ≠ j) (c : ℂ) : tv hij c * tv hij c = tv hij (2 * c) := by
  ext1
  simp only [tv, Units.val_mul]
  rw [transvection_mul_transvection_same _ _ hij, two_mul]

theorem dg_mul_tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) (d : Fin n → ℂˣ) (hi : (d i : ℂ) = 2)
    (hj : (d j : ℂ) = 1) : dg d * tv hij c = tv hij (2 * c) * dg d := by
  ext1
  ext k l
  simp only [dg, tv, Units.val_mul, transvection, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : i = k <;> by_cases hl : j = l
  · subst hk hl
    simp [hij, hi, hj]
  · subst hk
    simp [hl]
    split_ifs with h <;> simp only [h]
  · subst hl
    simp [hk]
    split_ifs with h <;> simp only [h]
  · simp [hk, hl]
    split_ifs with h <;> simp only [h]

theorem char_ne_zero {H : Type*} [Group H] (χ : H →* ℝ≥0) (g : H) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem char_tv (χ : GL (Fin n) ℂ →* ℝ≥0) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    χ (tv hij c) = 1 := by
  have h1 : χ (tv hij c) * χ (tv hij c) = χ (tv hij (2 * c)) := by rw [← map_mul, tv_mul]
  let d : Fin n → ℂˣ := fun k => if k = i then Units.mk0 2 two_ne_zero else 1
  have hi : (d i : ℂ) = 2 := by simp [d]
  have hj : (d j : ℂ) = 1 := by simp [d, hij.symm]
  have h2 : χ (dg d) * χ (tv hij c) = χ (tv hij (2 * c)) * χ (dg d) := by
    rw [← map_mul, ← map_mul, dg_mul_tv hij c d hi hj]
  have h3 : χ (tv hij c) = χ (tv hij (2 * c)) := by
    rw [mul_comm (χ (tv hij (2 * c)))] at h2
    exact mul_left_cancel₀ (char_ne_zero χ _) h2
  have h4 : χ (tv hij c) * χ (tv hij c) = χ (tv hij c) * 1 := by rw [mul_one, h1, h3]
  exact mul_left_cancel₀ (char_ne_zero χ _) h4

theorem char_dg (χ : GL (Fin n) ℂ →* ℝ≥0) (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1)
    (d : Fin n → ℂˣ) : χ (dg d) = 1 := by
  let D : (Fin n → ℂˣ) →* GL (Fin n) ℂ :=
    { toFun := dg, map_one' := dg_one, map_mul' := dg_mul }
  have hperm : ∀ σ : Equiv.Perm (Fin n), χ (dg (d ∘ σ)) = χ (dg d) := by
    intro σ
    have h := congrArg χ (pm_mul_dg σ d)
    rw [map_mul, map_mul, mul_comm (χ (pm σ))] at h
    exact (mul_right_cancel₀ (char_ne_zero χ (pm σ)) h).symm
  obtain ⟨v, hv_def⟩ : ∃ v : Fin n → ℂˣ, v = ∏ σ : Equiv.Perm (Fin n), d ∘ σ := ⟨_, rfl⟩
  have hv : ∀ k l, v k = v l := by
    intro k l
    rw [hv_def, Finset.prod_apply, Finset.prod_apply]
    exact Fintype.prod_equiv (Equiv.mulRight (Equiv.swap k l)) _ _
      (fun σ => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right])
  have hcent : ∀ g, dg v * g = g * dg v := by
    intro g
    ext1
    ext k l
    simp only [dg, Units.val_mul, diagonal_mul, mul_diagonal]
    rw [hv k l, mul_comm]
  have h1 : χ (dg v) = 1 := hz _ hcent
  have h2 : χ (dg v) = χ (dg d) ^ (Fintype.card (Equiv.Perm (Fin n))) := by
    have e : χ (dg v) = (χ.comp D) v := rfl
    rw [e, hv_def, map_prod]
    simp only [MonoidHom.comp_apply, D, MonoidHom.coe_mk, OneHom.coe_mk, hperm]
    rw [Finset.prod_const, Finset.card_univ]
  have hm : Fintype.card (Equiv.Perm (Fin n)) ≠ 0 := Fintype.card_ne_zero
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (by simp) hm).1 h2.symm

theorem char_eq_one (χ : GL (Fin n) ℂ →* ℝ≥0)
    (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1) (g : GL (Fin n) ℂ) : χ g = 1 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL (Fin n) ℂ, (u : Matrix (Fin n) (Fin n) ℂ) = M → χ u = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) ?_ ?_ ?_ ?_ g rfl
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  · intro D hD u hu
    rw [det_diagonal] at hD
    have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = dg (fun i => Units.mk0 (D i) (hD' i)) := by
      ext1
      simp [hu, dg]
    rw [hu']
    exact char_dg χ hz _
  · intro t u hu
    have hu' : u = tv t.hij t.c := by
      ext1
      simp [hu, tv, Matrix.TransvectionStruct.toMatrix]
    rw [hu']
    exact char_tv χ t.hij t.c
  · intro A B hA hB hPA hPB u hu
    obtain ⟨a, rfl⟩ : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
    obtain ⟨b, rfl⟩ : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
    have hu' : u = a * b := by
      ext1
      simp [hu]
    rw [hu', map_mul, hPA a rfl, hPB b rfl, one_mul]

theorem unimod : PositivityTheory.RgBcC.Unimod := by
  intro n _ _ μ _
  haveI : T2Space (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (PositivityTheory.RgTw.G n) :=
    (Units.isClosedEmbedding_embedProduct :
      Topology.IsClosedEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).locallyCompactSpace
  haveI : SecondCountableTopology (PositivityTheory.RgTw.G n) :=
    (Units.isEmbedding_embedProduct :
      Topology.IsEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).secondCountableTopology
  have hmap : ∀ g : PositivityTheory.RgTw.G n,
      Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
    intro g
    have e1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ g
    rw [← e2] at e1
    exact e1
  have hχ : ∀ g : PositivityTheory.RgTw.G n, Measure.modularCharacter g = 1 := by
    refine char_eq_one Measure.modularCharacter ?_
    intro z hz
    have hc : Measure.map (· * z) μ = μ := by
      have h : (fun x => x * z) = (fun x => z * x) := funext fun x => (hz x).symm
      rw [h, map_mul_left_eq_self]
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ z
    simp only [hc, Measure.haarScalarFactor_self] at e2
    exact e2
  have hR : μ.IsMulRightInvariant := ⟨fun g => by rw [hmap, hχ g, one_smul]⟩
  exact ⟨hR, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ⟩

end GlobalTheory.CompanionTheory.GLUnimod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_le_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal | exact GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal | (intros; apply GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_fk (l : ℕ) [Fact l.Prime] (k : ℕ) (w : Ainf l) :
    Lat.dk l k (Lat.fk l (k + 1) w) = Lat.fk l k w := by
  simp only [Lat.dk, Lat.fk, RingHom.comp_apply]
  exact Ideal.Quotient.factor_mk _ _

theorem dk_dpE (l : ℕ) [Fact l.Prime] (M k i : ℕ) :
    Lat.dk l k (Lat.dpE (Lat.fk l (k + 1)) (xi0 l) l M i) = Lat.dpE (Lat.fk l k) (xi0 l) l M i := by
  simp only [Lat.dpE, Lat.η, map_rat_smul, map_pow, dk_fk]

theorem dk_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) :
    ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro x hx
  have hle : Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M ≤
      (Lat.sub (Lat.fk l k) (xi0 l) l M).comap (Lat.dk l k) := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_fk]
      exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_dpE]
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  exact hle hx

end GlobalTheory.CompanionTheory.LatLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem sigmaB_fixes_K {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : ∀ g (a : K),
    (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  intro g a
  have key : gP l g (kP l K a) = kP l K a := by
    have h1 : galBdRHom (toBot g.1) (algClToBdR l (a : PadicAlgCl l))
        = algClToBdR l ((toBot g.1) (a : PadicAlgCl l)) :=
      gal_smul_algClToBdR (toBot g.1) (a : PadicAlgCl l)
    have h2 : (toBot g.1) (a : PadicAlgCl l) = (a : PadicAlgCl l) := g.2 a
    rw [h2] at h1
    exact h1
  change gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  change Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = Ideal.Quotient.mk _ (kP l K a)
  rw [Ideal.quotientMap_mk, key]

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem gP_kP {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (x : K) : gP l g (kP l K x) = kP l K x := by
  have h1 : (toBot g.1) • algClToBdR l (K.val x) = algClToBdR l ((toBot g.1) (K.val x)) :=
    gal_smul_algClToBdR _ _
  have h2 : (toBot g.1) (K.val x) = K.val x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
  rw [h2] at h1
  exact h1

theorem sigA_fix : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  intro l _ K M h k g a
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  show Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = _
  rw [Ideal.quotientMap_mk, gP_kP]
  rfl

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem iota_algebraMap_OK : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  intro l _ K M h k a
  rfl

end GlobalTheory.CompanionTheory.LatC
end

