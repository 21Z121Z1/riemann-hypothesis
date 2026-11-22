import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLatticeStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_selfDual_of_selfDual_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → ∀ z : Fin n → RA F E, (∀ y ∈ L, hermA c G z (fv F y) ∈ hat1 F (J : Set E)) ↔ z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_selfDual | exact GlobalTheory.AdLat.hat_selfDual | (intros; apply GlobalTheory.AdLat.hat_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdmissibleFalseIffFirstInvariant
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDatumEq

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def cls (l : Level H) {n : ℕ} (x : Fin n → D.La) : Fin n → ConjCl D l := fun b => Submodule.Quotient.mk (x b)

theorem cls_surjective (l : Level H) (n : ℕ) : Function.Surjective (cls (D := D) l (n := n)) := fun a =>
  ⟨fun b => qRep (a b), funext fun b => Classical.choose_spec (Submodule.Quotient.mk_surjective _ (a b))⟩

theorem cls_neg {n : ℕ} (x : Fin n → D.La) : cls l (-x) = -cls l x := by
  funext b; simp [cls]

theorem isSep_cSep (l : Level H) : IsSep l (cSep l) := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := exists_isSep l
  rw [cSep, dif_pos h]
  exact h.choose_spec

theorem mk_levRep (q : LevQ D l) : (Submodule.Quotient.mk (levRep q) : NamedCl D l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem levPt_levRep (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (q : LevQ D l) :
    levPt Xo x0 (levRep q) = levPtCl Xo x0 q := by
  rw [← levPtCl_mk, mk_levRep]

theorem pairL_cast {n : ℕ} (x0 x : Fin n → D.La) :
    ((pairL (l := l) x0 x : ℤ) : ZMod l.M) = pairing D l (cls l x0) (fun b => Submodule.Quotient.mk (x b)) := by
  simp only [pairL, pairing, cls, Int.cast_sum, pairOne_mk D l (isSep_cSep l)]

theorem pairL_levRep {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    ((pairL (l := l) x0 (fun b => levRep (q b)) : ℤ) : ZMod l.M) = pairing D l (cls l x0) q := by
  rw [pairL_cast]; simp only [mk_levRep]

theorem zetaM_eq (c : Coeff l) : Formalism.L2.Pj.zetaM c = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM' hk
  have hd : l.M' / l.M = k := by rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)]
  apply Subtype.ext
  rw [Formalism.L2.Pj.zetaM, hd, GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM]
  change zeta l.M' ^ k = zeta l.M
  rw [zeta, zeta, ← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  have : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  push_cast
  field_simp

theorem zeta_zpow (c : Coeff l) (m : ℤ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ m = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ (m : ZMod l.M).val := by
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  have hz := zetaM_prim c
  have hne : GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ≠ 0 := hz.ne_zero (NeZero.ne _)
  rw [← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv m l.M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hz.pow_eq_one, one_zpow, _root_.mul_one]

theorem datum_eq_character_pairing (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c x0 q = eChar D c (cls l x0) q := by
  rw [x0Dat, eChar, zetaM_eq, zeta_zpow, pairL_levRep]

theorem datum_neg_eq_inv (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c (-x0) q = (x0Dat c x0 q)⁻¹ := by
  simp only [x0Dat, ← zpow_neg]
  congr 1
  simp [pairL]

theorem indCoeff_cls (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    indCoeff c (cls l x0) q = (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c (-x0) q := by
  rw [indCoeff_eq, datum_neg_eq_inv, datum_eq_character_pairing, eChar]

theorem normalized_datum_eq_induced_coeff (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c x0 q = indCoeff c (-cls l x0) q := by
  rw [← cls_neg, indCoeff_cls, neg_neg]

end GlobalTheory.ShortDatumEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion
section
namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem exists_factor_openImmersion {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (j : Sp R ⟶ X)
    [IsOpenImmersion j] (x : Sp S ⟶ X) (p : Sp S) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] (lam : S →+* T), IsUnit (lam g) →
      ∃ ψ : R →+* T, spMap lam ≫ x = spMap ψ ≫ j := by
  have hU : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hU
  refine ⟨g, hpg, fun T _ lam hu => ?_⟩
  have hr : Set.range (spMap lam ≫ x) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap lam q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    exact hsub hq
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j (spMap lam ≫ x) hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem openChart_factor_near_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R), OpenChart j y₀ → ∀ (S : Type) [CommRing S] [Algebra c.F S] (xF : Sp S ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) → ∀ p : Sp S, xF p ∈ Set.range j → ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) → ∃ ψ : R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j := by
  intro E _ _ _ H Dw l Xo c R _ _ j y₀ hj S _ _ xF hx p hp
  haveI := hj.1
  obtain ⟨g, hg, h⟩ := exists_factor_openImmersion j xF p hp
  refine ⟨g, hg, fun T _ _ lam hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := h T lam.toRingHom hu
  have h2 := congrArg (· ≫ pullback.snd _ _) hψ
  simp only [Category.assoc] at h2
  rw [hx, hj.2.2, ← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ ψ with commutes' := fun a => ?_ }, hψ⟩
  have h4 := RingHom.congr_fun h3 a
  exact h4.symm.trans (lam.commutes a)

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Tower

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
lemma fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i; simp [fv, TensorProduct.tmul_sub]

omit [NumberField E] in
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i; simp [fv]

omit [NumberField E] in
lemma fv_nsmul (N : ℕ) (x : Fin n → E) : fv F (N • x) = N • fv F x := by
  induction N with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

omit [NumberField E] in
lemma fv_smul (c : 𝓞 E) (x : Fin n → E) :
    fv F (c • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • fv F x := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

omit [NumberField E] in
lemma nsmul_cancel {N : ℕ} (hN : 0 < N) {z u : Fin n → RA F E} (h : N • z = N • u) : z = u := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun t => (N : F)⁻¹ • t) h
  simpa [smul_smul, inv_mul_cancel₀ hN'] using this

omit [NumberField E] in
lemma smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (c : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma exists_div {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ v, fv F v ∈ hat F (M : Set (Fin n → E)) ↔ v ∈ M) {N : ℕ} (hN : 0 < N)
    (x : M) {u : Fin n → RA F E} (hu : u ∈ hat F (M : Set (Fin n → E)))
    (h : fv F (x : Fin n → E) = N • u) : ∃ v : M, x = N • v := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u := by
    apply nsmul_cancel hN
    rw [← fv_nsmul, h1, h]
  refine ⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩
  exact h1.symm

lemma projective_of_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Module.Projective (𝓞 E) L := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) L := inferInstance
  exact Module.Flat.projective_of_finitePresentation

omit [NumberField E] in
lemma mulVec_nsmul (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) (z : Fin n → RA F E) :
    g *ᵥ (N • z) = N • (g *ᵥ z) := map_nsmul g.mulVecLin N z

def rel (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) :
    Submodule (𝓞 E) (L × Λ) where
  carrier := {p | ∃ w ∈ hat F (L : Set (Fin n → E)),
    fv F (p.2 : Fin n → E) = g *ᵥ (fv F (p.1 : Fin n → E) + N • w)}
  zero_mem' := ⟨0, zero_mem _, by simp [fv_zero]⟩
  add_mem' := by
    rintro p q ⟨w, hw, hp⟩ ⟨w', hw', hq⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, fv_add, hp, hq]
    rw [← Matrix.mulVec_add, smul_add]
    congr 1
    abel
  smul_mem' := by
    rintro c p ⟨w, hw, hp⟩
    refine ⟨_, smul_mem_hat L c hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, fv_smul, hp]
    rw [← Matrix.mulVec_smul, smul_add, smul_comm]

end GlobalTheory.AdLat.Tower

open GlobalTheory.AdLat.Tower in
theorem GlobalTheory.AdLat.exists_linear_approx_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (Λ : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L → ∃ f : ℕ → (L →ₗ[𝓞 E] Λ), (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (L : Set (Fin n → E))), fv F (f N a : Fin n → E) = (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (a : Fin n → E) + N • w)) ∧ (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧ ∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v := by
  intro F E _ _ _ _ _ n L g Λ hL hsp hΛ
  obtain ⟨Λ', h1, hΛfg, hΛsp, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨hLc, hLa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hsp
  obtain ⟨hΛc, hΛa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛfg hΛsp
  set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG
  have hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E)) := by
    intro u hu
    rw [← SetLike.mem_coe, hhat]
    exact ⟨u, hu, rfl⟩
  have hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z := by
    intro z hz
    rw [← SetLike.mem_coe, hhat] at hz
    exact hz
  have hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h
    simp only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    exact this
  haveI := projective_of_fg L hL
  have key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact ⟨0, fun h => absurd h (by omega)⟩
    have hsurj : Function.Surjective
        ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype) := by
      intro a
      obtain ⟨x, hx, w, hw, e⟩ := hΛa N hN _ (hto _ ((hLc a).2 a.2))
      obtain ⟨u, hu, rfl⟩ := hfrom w hw
      refine ⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]
      simp
    obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
    refine ⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩
    obtain ⟨w, hw, e⟩ := (s a).2
    have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
    rw [ha] at e
    exact ⟨w, hw, e⟩
  choose f hf using key
  refine ⟨f, hf, ?_, ?_⟩
  · intro N m hN hm a
    obtain ⟨w, hw, e⟩ := hf N hN a
    obtain ⟨w', hw', e'⟩ := hf (N * m) (Nat.mul_pos hN hm) a
    obtain ⟨v, hv⟩ := exists_div hΛc hN (f (N * m) a - f N a)
      (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by
        rw [Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub,
          mul_smul]
        congr 1
        abel)
    exact ⟨v, by rw [← hv]; abel⟩
  · intro N hN
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, e⟩ := hf N hN a
      obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc v).2 v.2)
      have e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u) := by
        rw [mulVec_nsmul, eu, ← fv_nsmul, hv]; rfl
      have e3 := hinj _ _ (e.symm.trans e2)
      exact exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)
    · rintro ⟨v, rfl⟩
      exact ⟨f N v, map_nsmul _ _ _⟩
    · obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc a').2 a'.2)
      obtain ⟨x, hx, w, hw, rfl⟩ := hLa N hN u hu
      obtain ⟨w', hw', e'⟩ := hf N hN ⟨x, hx⟩
      obtain ⟨v, hv⟩ := exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by
        rw [Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]
        congr 1
        abel)
      exact ⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section
namespace GlobalTheory.Frames

theorem spMap_dualMap_left {R T T' : Type} [CommRing R] [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
    (ρ : T →ₐ[R] T') : (Chart.spMap (SqZero.dualMap ρ)).left = spMap (dualMap (ρ : T →+* T')) := by
  rw [Chart.spMap_left]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem existsUnique_glue_dual_of_isTerminal {R : Type} [CommRing R] (hR : IsTerminal (Sp R)) {S : Type} [CommRing S]
    [Algebra R S] (Y : Scheme.{0}) {κ : Type} (h : κ → S) (hs : Ideal.span (Set.range h) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y)
    (hw : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) :
    ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  let X : Over (Spec (CommRingCat.of R)) := Over.mk (hR.from Y)
  let w' : ∀ i, Chart.sp (R₀ := R) (DualNumber (Localization.Away (h i))) ⟶ X := fun i =>
    Over.homMk (w i) (hR.hom_ext _ _)
  let q : ∀ k, S →ₐ[R] Localization.Away (h k) := fun k => SqZero.awayHom R (h k)
  have hq : ∀ k, SqZero.IsAway (q k) (h k) := fun k => SqZero.isAway_awayHom _
  let p : ∀ k l, S →ₐ[R] Localization.Away (h k * h l) := fun k l => SqZero.awayHom R (h k * h l)
  have hp : ∀ k l, SqZero.IsAway (p k l) (h k * h l) := fun k l => SqZero.isAway_awayHom _
  choose a ha using fun k l => (hq k).lift (p k l)
    (isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact (hp k l).unit))
  choose b hb using fun k l => (hq l).lift (p k l)
    (isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact (hp k l).unit))
  have hs' := SqZero.span_range_map hs (SqZero.inlS R S)
  obtain ⟨z, hz⟩ := SqZero.away_glue (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) w' (fun k l =>
      SqZero.agree_of_isAway (hq k).dualMap (hq l).dualMap (a₀ := SqZero.dualMap (a k l))
        (b₀ := SqZero.dualMap (b k l)) (by rw [SqZero.dualMap_comp, SqZero.dualMap_comp, ha, hb])
        (by rw [SqZero.dualMap_comp, ha, ← map_mul]; exact (hp k l).dualMap)
        (Over.OverMorphism.ext (by
          rw [Over.comp_left, Over.comp_left, spMap_dualMap_left, spMap_dualMap_left]
          exact hw k l _ _ (RingHom.ext fun x => AlgHom.congr_fun (ha k l) x)
            (RingHom.ext fun x => AlgHom.congr_fun (hb k l) x))))
  have hz' : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ z.left = w i := fun i => by
    have : (Chart.spMap (SqZero.dualMap (q i))).left ≫ z.left = w i := congrArg CommaMorphism.left (hz i)
    rw [spMap_dualMap_left] at this
    exact this
  refine ⟨z.left, hz', fun y hy => ?_⟩
  let y' : Chart.sp (R₀ := R) (DualNumber S) ⟶ X := Over.homMk y (hR.hom_ext _ _)
  have : y' = z := SqZero.away_ext (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) fun k => Over.OverMorphism.ext (by
      rw [Over.comp_left, Over.comp_left, spMap_dualMap_left]
      exact (hy k).trans (hz' k).symm)
  exact congrArg CommaMorphism.left this

theorem existsUnique_glue_dual : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i :=
  fun _ _ Y _ h hs w hw => existsUnique_glue_dual_of_isTerminal specZIsTerminal Y h hs w hw

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
section
noncomputable section

namespace GlobalTheory.Frames.SecPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_pull_linComb {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (e : (fun k => h ≫ φ k) = φ') (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ h ⁻¹ᵁ (LB.LinComb L φ ε).U j), (h.appLE _ _ hle).hom (s.f j) = s'.f j := by
  subst e
  exact ⟨DVR.pullSec L φ ε s h, fun _ _ => rfl⟩

theorem lbSec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem ppx_chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem res_res_top {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (g : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom g := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem scal_res {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i j : (PPx x).ι) :
    ((Gx x).presheaf.map (homOfLE (inf_le_left : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U i)).op).hom (scal x a i) =
      ((Gx x).presheaf.map (homOfLE (inf_le_right : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U j)).op).hom
        (scal x a j) := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun]
  rw [res_res_top, res_res_top]

def gxMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') : Gx x' ⟶ Gx x :=
  ((Over.homMk (spMap ψ) h : Over.mk x' ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem gxMap_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_snd]

theorem gxMap_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap ψ := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  rfl

theorem gx_hom_ext {S : Type} [CommRing S] {W : Scheme.{0}} {x : Sp S ⟶ Xo.X} (f₁ f₂ : W ⟶ Gx x)
    (h₁ : f₁ ≫ (fst (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f₁ ≫ (snd (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f₁ = f₂ :=
  Over.tensorObj_ext f₁ f₂ h₁ h₂

def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) where
  f i := scal x a i * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, scal_res x a i j]
    ring

theorem existsUnique_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  intro E _ _ _ H Dw l Xo S T _ _ φ a x x' hx s
  have hs := gxMap_snd φ x x' hx.symm
  have hf := gxMap_fst φ x x' hx.symm
  obtain ⟨s', hs'⟩ := exists_pull_linComb Xo.univ.t.PP.L (K := Fin 1)
    (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (snd (Over.mk x') Xo.univ.t.G).left) _
    (gxMap φ x x' hx.symm) (funext fun _ => hs) (scalSec x a s)
  refine ⟨s', ⟨_, hs, hf, hs'⟩, ?_⟩
  rintro t ⟨pm, ps, pf, ht⟩
  obtain rfl : pm = gxMap φ x x' hx.symm :=
    gx_hom_ext _ _ (pf.trans hf.symm) (ps.trans hs.symm)
  exact lbSec_ext fun i => (ht i (ppx_chart_le _ hs i)).symm.trans (hs' i (ppx_chart_le _ hs i))

end GlobalTheory.Frames.SecPull
end
end

