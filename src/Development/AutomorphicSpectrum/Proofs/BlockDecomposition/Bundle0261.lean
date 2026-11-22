import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (B : Type) [CommRing B] [Algebra R B] :
    ∃ (A' : Over (Sp B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R B)) := by
  have h := isGrpPullback_pullback A (spMap (algebraMap R B))
  obtain ⟨h1, h2⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ _ _ _ g h hA hg
  exact ⟨_, inferInstance, _, h1, h2, h.1⟩

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem vb_of_bijective' {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F') n) : VB R (H1 F) n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {n : ℕ} (h : VB k M n) :
    Module.finrank k M = n := by
  obtain ⟨hf, -, hr⟩ := h
  have e := hr ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem first_cohomology_vector_bundle_rank : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle := by
  intro hD hL hB hP hS hK hT hV R _ A _ g hA hg
  have : IsProper A.hom := hA.proper
  have : IsSeparated A.hom := inferInstance
  have : Smooth A.hom := hg.smooth
  obtain ⟨P, iP, fP, S, hPerf⟩ := hP R A.left A.hom inferInstance inferInstance
  have low : ∀ {R₀ : Type} [CommRing R₀] (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
      ∀ (S₀ : Sys A₀.left P), Function.Bijective (resSys A₀.hom S₀).pull1 ∧
        (Stein (OAff A₀.hom) ↔ Stein (OSys A₀.hom S₀)) := fun {R₀} _ A₀ _ h₀ S₀ => by
    have : IsProper A₀.hom := h₀.proper
    obtain ⟨b1, -, st⟩ := hL R₀ _ _ _ _ _ (hD R₀ A₀.left A₀.hom inferInstance P S₀)
    exact ⟨b1, st⟩
  refine vb_of_bijective' (resSys A.hom S) (low A hA S).1 (hV R P (OSys A.hom S) g hPerf ?_ ?_ ?_)
  · intro R' _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg R'
    obtain ⟨S', m, -⟩ := hB R R' A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, (low A' hA' S').2.1 (hS R' A' g hA' hg')⟩
  · intro k _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg k
    obtain ⟨S', m, -⟩ := hB R k A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, finrank_of_vb
      (vb_of_bijective _ (low A' hA' S').1 (hK k A' g hA' hg' (Field.toIsField k)))⟩
  · intro B _ _ _ t ht
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg B
    obtain ⟨S', m, -⟩ := hB R B A.left A'.left A.hom A'.hom φ h inferInstance P S
    obtain ⟨A'', _, φ', hA'', hg'', h'⟩ := exists_base A' hA' hg' (B ⧸ Ideal.span {t})
    have : IsProper A'.hom := hA'.proper
    obtain ⟨S'', m', hm'⟩ := hB B (B ⧸ Ideal.span {t}) A'.left A''.left A'.hom A''.hom φ' h' inferInstance P S'
    refine ⟨OSys A'.hom S', m, OSys A''.hom S'', m', fun y => ?_⟩
    have b2 := (low A'' hA'' S'').1
    obtain ⟨d, rfl⟩ := b2.2 y
    obtain ⟨c, hc⟩ := hT B A' g hA' hg' t ht A''.left A''.hom φ' h' d
    refine ⟨(resSys A'.hom S').pull1 c, ?_⟩
    obtain ⟨d', hd'⟩ := b2.2 (m'.coef.pull1 ((resSys A'.hom S').pull1 c))
    have e := (existsUnique_isPullO h'.w c).unique hc (hm' c d' hd'.symm)
    rw [e, hd']

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeight
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem finite_units_zpow_eq {F : Type*} [Field F] {d : ℤ} (hd : d ≠ 0) (w : Fˣ) :
    {z : Fˣ | z ^ d = w}.Finite := by
  have hm : 0 < d.natAbs := Int.natAbs_pos.2 hd
  have key : ∀ c : F, {z : Fˣ | (z : F) ^ d.natAbs = c}.Finite := fun c =>
    ((Polynomial.nthRoots d.natAbs c).toFinset.finite_toSet.preimage
      (Units.val_injective (α := F)).injOn).subset fun z hz => by
        simpa [Polynomial.mem_nthRoots hm] using hz
  rcases Int.natAbs_eq d with h | h
  · refine (key (w : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = w
    rw [← Units.val_pow_eq_pow_val, hz']
  · refine (key ((w⁻¹ : Fˣ) : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_neg, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = ((w⁻¹ : Fˣ) : F)
    rw [← Units.val_pow_eq_pow_val, ← hz', inv_inv]

theorem eq_one_of_tpow_mul_unit_eigen {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l))
    [FiniteDimensional ℚ_[l] ↥L]
    (hI : ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite)
    (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l])
    (hact : ∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)))
    (hin : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) :
    n = 1 := by
  by_contra hn
  have ht : GroundTheory.PAdicHodge.tBdR l ≠ 0 := (GroundTheory.PAdicHodge.irreducible_tBdR (p := l)).ne_zero
  let c : ℤ_[l]ˣ →* ℚ_[l]ˣ := Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom
  have hc : Function.Injective c := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  let χ : Gal(Om l/↥L) → ℚ_[l] := fun σ => (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])
  have hχ : ∀ σ, χ σ ≠ 0 := fun σ => (c (GroundTheory.PAdicHodge.cycloChar L σ)).ne_zero
  let A : ℚ_[l] →+* Formalism.Per6.BdRp l := algebraMap ℚ_[l] (Formalism.Per6.BdRp l)
  have hu : ∀ σ : Gal(Om l/↥L), A (χ σ) ^ n * (σ • (u : Formalism.Per6.BdRp l)) = A (a σ) * u := by
    intro σ
    have h := hact σ
    rw [smul_mul', smul_pow', GroundTheory.PAdicHodge.gal_smul_tBdR, mul_pow] at h
    refine mul_left_cancel₀ (pow_ne_zero n ht) ?_
    change _ = _ at h
    linear_combination h
  have hu' : ∀ σ : Gal(Om l/↥L), σ • (u : Formalism.Per6.BdRp l) = A (a σ * (χ σ ^ n)⁻¹) * u := by
    intro σ
    have e : A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n (hχ σ)), map_one]
    calc σ • (u : Formalism.Per6.BdRp l)
        = (A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n) * (σ • (u : Formalism.Per6.BdRp l)) := by rw [e, one_mul]
      _ = A ((χ σ ^ n)⁻¹) * (A (a σ) * u) := by rw [mul_assoc, hu]
      _ = A (a σ * (χ σ ^ n)⁻¹) * u := by rw [map_mul]; ring
  have hx0 : GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) ≠ 0 :=
    (u.isUnit.map (GroundTheory.PAdicHodge.thetaAlgHom l)).ne_zero
  have hθ : ∀ (σ : Gal(Om l/↥L)) (q : ℚ_[l]),
      σ • (u : Formalism.Per6.BdRp l) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) q * u →
        σ • GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) =
          algebraMap ℚ_[l] ℂ_[l] q * GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) := by
    intro σ q h
    rw [GroundTheory.PAdicHodge.thetaAlgHom_apply, ← GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul, h,
      ← GroundTheory.PAdicHodge.thetaAlgHom_apply, map_mul, AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := GroundTheory.PAdicHodge.EigenChar.exists_eigenChar hx0
    fun σ : Gal(Om l/↥L) => ⟨_, hθ σ _ (hu' σ)⟩
  have hfin := GroundTheory.PAdicHodge.ACris.senTateCharacters (p := l) L ψ hψc _ hx0 hψx
  have hd : (1 - (n : ℤ)) ≠ 0 := fun h => hn (by omega)
  have hψ : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      (c (GroundTheory.PAdicHodge.cycloChar L σ)) ^ (1 - (n : ℤ)) = ψ σ := by
    intro σ hσ
    have h2 : a σ * (χ σ ^ n)⁻¹ = ψ σ := GroundTheory.PAdicHodge.EigenChar.eq_of_mul_eq hx0
      ((hθ σ _ (hu' σ)).symm.trans (hψx σ))
    refine Units.ext ?_
    rw [Units.val_zpow_eq_zpow_val, ← h2, hin σ hσ]
    change χ σ ^ (1 - (n : ℤ)) = χ σ * (χ σ ^ n)⁻¹
    rw [zpow_sub₀ (hχ σ), zpow_one, zpow_natCast, div_eq_mul_inv]
  refine (hI.image hc.injOn) (Set.Finite.of_finite_fibers (fun z => z ^ (1 - (n : ℤ))) ?_ ?_)
  · refine hfin.subset ?_
    rintro _ ⟨_, ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (hψ σ hσ).symm⟩
  · intro w _
    refine (finite_units_zpow_eq hd w).subset fun z hz => ?_
    exact hz.2

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateEventuallyZero
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Nonv

theorem ltIter_succ_eq {B : Type} [CommRing B] (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  simp only [ltIter, Function.iterate_succ_apply']

theorem norm_step_eq {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q)
    (h : ‖c‖ ^ (q - 1) < ‖a‖) : ‖a * c + c ^ q‖ = ‖a‖ * ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    have : q ≠ 0 := by omega
    simp [this]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hlt : ‖c ^ q‖ < ‖a * c‖ := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [norm_pow, norm_mul, pow_succ]
      simp only [Nat.add_sub_cancel] at h
      exact mul_lt_mul_of_pos_right h hcpos
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le, norm_mul]

theorem norm_step_le {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q) :
    ‖a * c + c ^ q‖ ≤ max ‖a‖ (‖c‖ ^ (q - 1)) * ‖c‖ := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [norm_mul, norm_pow, pow_succ, max_mul_of_nonneg _ _ (norm_nonneg c)]

theorem exists_norm_geometric {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) (q : ℕ) (hq : 2 ≤ q)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (c : ℕ → C) (hc : ∀ n, c (n + 1) = a * c n + c n ^ q)
    (h0 : ‖c 0‖ < 1) : ∃ n, ∀ j, ‖c (n + j)‖ = ‖a‖ ^ j * ‖c n‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set ρ := max ‖a‖ (‖c 0‖ ^ (q - 1)) with hρ
  have hρ1 : ρ < 1 := max_lt ha (pow_lt_one₀ (norm_nonneg _) h0 (by omega))
  have hρ0 : 0 ≤ ρ := hapos.le.trans (le_max_left _ _)
  have hdec : ∀ n, ‖c n‖ ≤ ρ ^ n * ‖c 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖c n‖ ≤ ‖c 0‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hm : max ‖a‖ (‖c n‖ ^ (q - 1)) ≤ ρ :=
        max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle _)
      rw [hc n]
      calc ‖a * c n + c n ^ q‖ ≤ max ‖a‖ (‖c n‖ ^ (q - 1)) * ‖c n‖ := norm_step_le a _ q hq
        _ ≤ ρ * (ρ ^ n * ‖c 0‖) := mul_le_mul hm ih (norm_nonneg _) hρ0
        _ = ρ ^ (n + 1) * ‖c 0‖ := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hapos hρ1
  have hcn : ‖c n‖ < ‖a‖ :=
    ((hdec n).trans (mul_le_of_le_one_right (pow_nonneg hρ0 n) h0.le)).trans_lt hn
  have hsmall : ∀ x : C, ‖x‖ ≤ ‖c n‖ → ‖x‖ ^ (q - 1) < ‖a‖ := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := hx.trans (hcn.trans ha).le
    exact ((pow_le_of_le_one (norm_nonneg _) hx1 (by omega)).trans hx).trans_lt hcn
  refine ⟨n, fun j => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : ‖c (n + j)‖ ≤ ‖c n‖ := by
      rw [ih]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hapos.le ha.le)
    rw [← add_assoc, hc (n + j), norm_step_eq a _ q hq (hsmall _ hle), ih]
    ring

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem ltIter_mem (hE : PerEnv S F ϖ) (q : ℕ) {Q : B} (hQ : Q ∈ S) (n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [ltIter_succ_eq]
    exact S.add_mem (S.mul_mem hE.mem ih) (S.pow_mem ih q)

theorem ltIter_mem_succ (hE : PerEnv S F ϖ) (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (q : ℕ) (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S)
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) (n m : ℕ) (hm : 1 ≤ m)
    (hy : ltIter ϖ q n Q ∈ F m) : ltIter ϖ q n Q ∈ F (m + 1) := by
  have hanti : Antitone F := antitone_nat_of_succ_le hE.anti
  have hD : ∀ j, ltIter ϖ q (n + j) Q - ϖ ^ j * ltIter ϖ q n Q ∈ F (m + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hym : ltIter ϖ q (n + j) Q ∈ F m := by
        have h1 := (F m).add_mem (hE.anti m ih) ((F m).mul_mem_left (ϖ ^ j) hy)
        simpa using h1
      have hsq : ltIter ϖ q (n + j) Q * ltIter ϖ q (n + j) Q ∈ F (m + 1) :=
        hanti (by omega : m + 1 ≤ m + m) (hE.mul_le m m (Ideal.mul_mem_mul hym hym))
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
      have he : ltIter ϖ (r + 2) (n + (j + 1)) Q - ϖ ^ (j + 1) * ltIter ϖ (r + 2) n Q =
          ϖ * (ltIter ϖ (r + 2) (n + j) Q - ϖ ^ j * ltIter ϖ (r + 2) n Q) +
            ltIter ϖ (r + 2) (n + j) Q ^ r * (ltIter ϖ (r + 2) (n + j) Q * ltIter ϖ (r + 2) (n + j) Q) := by
        rw [← add_assoc, ltIter_succ_eq]
        ring
      rw [he]
      exact (F (m + 1)).add_mem ((F (m + 1)).mul_mem_left _ ih) ((F (m + 1)).mul_mem_left _ hsq)
  obtain ⟨c, hc⟩ := hT (m + 1)
  refine hE.closed (m + 1) _ (ltIter_mem hE q hQ n) fun M => ?_
  obtain ⟨N, hN⟩ := hc (M + c)
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  refine ⟨ϖ ^ n * s, S.mul_mem (S.pow_mem hE.mem n) hs, ?_⟩
  have h1 : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h2 : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h3 : ϖ ^ N * ϖ' ^ N = 1 := by rw [← mul_pow, hϖ, one_pow]
  have he : ltIter ϖ q n Q - ϖ ^ M * (ϖ ^ n * s) =
      ϖ ^ n * ϖ' ^ c * (ϖ ^ c * (ϖ' ^ (n + N) * ltIter ϖ q (n + N) Q - 0) - ϖ ^ (M + c) * s) -
        ϖ' ^ N * (ltIter ϖ q (n + N) Q - ϖ ^ N * ltIter ϖ q n Q) := by
    linear_combination (-ltIter ϖ q n Q) * h3 +
      (ϖ ^ M * ϖ ^ n * s - ϖ' ^ N * ltIter ϖ q (n + N) Q * (ϖ ^ n * ϖ' ^ n)) * h1 -
      ϖ' ^ N * ltIter ϖ q (n + N) Q * h2
  rw [he]
  exact (F (m + 1)).sub_mem ((F (m + 1)).mul_mem_left _ hd) ((F (m + 1)).mul_mem_left _ (hD N))

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem exists_ltIter_mem_one (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (θ : B →+* C) (hθ : ∀ x, θ x = 0 ↔ x ∈ F 1)
    (hS : ∀ s ∈ S, ‖θ s‖ ≤ 1) (ha : ‖θ ϖ‖ < 1) (q : ℕ) (hq : 2 ≤ q) (Q : B) (hQ : Q ∈ S)
    (hQM : ∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M))
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) : ∃ n, ltIter ϖ q n Q ∈ F 1 := by
  have haa : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
  have ha0 : θ ϖ ≠ 0 := left_ne_zero_of_mul_eq_one haa
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr ha0
  have hnn : ‖θ ϖ‖ * ‖θ ϖ'‖ = 1 := by rw [← norm_mul, haa, norm_one]
  have hpos' : 0 < ‖θ ϖ'‖ := by
    have := right_ne_zero_of_mul_eq_one haa
    exact norm_pos_iff.mpr this
  have h0 : ‖θ (ltIter ϖ q 0 Q)‖ < 1 := by
    obtain ⟨M, hM, s, hs, hd⟩ := hQM
    have e : θ Q ^ M = θ ϖ * θ s := by
      have := (hθ _).mpr hd
      simp only [map_sub, map_mul, map_pow, pow_one] at this
      exact sub_eq_zero.mp this
    by_contra hcon
    have h1 : (1 : ℝ) ≤ ‖θ Q‖ := by simpa [ltIter] using hcon
    have h2 : (1 : ℝ) ≤ ‖θ Q‖ ^ M := one_le_pow₀ h1
    have h3 : ‖θ Q‖ ^ M = ‖θ ϖ‖ * ‖θ s‖ := by rw [← norm_pow, e, norm_mul]
    have h4 : ‖θ ϖ‖ * ‖θ s‖ < 1 :=
      (mul_le_of_le_one_right hapos.le (hS s hs)).trans_lt ha
    linarith
  obtain ⟨n, hn⟩ := exists_norm_geometric (θ ϖ) q hq ha0 ha (fun n => θ (ltIter ϖ q n Q))
    (fun n => by simp only [ltIter_succ_eq, map_add, map_mul, map_pow]) h0
  refine ⟨n, (hθ _).mp ?_⟩
  by_contra hne
  have hcpos : 0 < ‖θ (ltIter ϖ q n Q)‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := hT 1
  have hK : 0 < ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hK ha
  obtain ⟨N, hN⟩ := hc m
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  have e := (hθ _).mpr hd
  simp only [map_sub, map_mul, map_pow, map_zero, sub_zero] at e
  have e2 : ‖θ ϖ‖ ^ c * (‖θ ϖ'‖ ^ (n + N) * ‖θ (ltIter ϖ q (n + N) Q)‖) = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    have := congrArg norm (sub_eq_zero.mp e)
    simpa only [norm_mul, norm_pow] using this
  have hNN : ‖θ ϖ‖ ^ N * ‖θ ϖ'‖ ^ N = 1 := by rw [← mul_pow, hnn, one_pow]
  have e3 : ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    rw [← e2, hn N, pow_add]
    linear_combination (-(‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖)) * hNN
  have h5 : ‖θ ϖ‖ ^ m * ‖θ s‖ ≤ ‖θ ϖ‖ ^ m :=
    mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hs)
  linarith

end GlobalTheory.CompanionTheory.LTPer.Nonv

namespace GlobalTheory.CompanionTheory.LTPer

open GlobalTheory.CompanionTheory.LTPer.Nonv in

theorem exists_ltIter_eq_zero_of_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0 → ∃ n, ltIter ϖ q n Q = 0 := by
  intro B _ S F ϖ C _ _ hE ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  obtain ⟨n, hn⟩ := exists_ltIter_mem_one ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  refine ⟨n, hE.sep _ fun k => ?_⟩
  have hall : ∀ m, 1 ≤ m → ltIter ϖ q n Q ∈ F m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih => exact ltIter_mem_succ hE ϖ' hϖ q hq hQ hT n m hm ih
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hE.top]; exact Submodule.mem_top
  · exact hall k hk

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruence
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.QLim

theorem map_mem {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {x : B}
    (hx : x ∈ S) : ϖ * x + x ^ q ∈ S :=
  S.add_mem (S.mul_mem hϖ hx) (S.pow_mem hx q)

theorem step_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) {a b c : B} (hb : b ∈ S) (hc : c ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hab : a - b = ϖ ^ m * c) :
    ∃ c' ∈ S, (ϖ * a + a ^ q) - (ϖ * b + b ^ q) = ϖ ^ (m + 1) * c' := by
  obtain ⟨s, hs, hqs⟩ := hq
  have hy : ϖ ^ m * c ∈ S := S.mul_mem (S.pow_mem hϖ m) hc
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ q : Polynomial S)
    (⟨b, hb⟩ : S) (⟨ϖ ^ m * c, hy⟩ : S)
  have hk' : (b + ϖ ^ m * c) ^ q =
      b ^ q + (q : B) * b ^ (q - 1) * (ϖ ^ m * c) + (k : B) * (ϖ ^ m * c) ^ 2 := by
    have h := congrArg (Subtype.val) hk
    simpa [Polynomial.derivative_X_pow] using h
  have ha : a = b + ϖ ^ m * c := by linear_combination hab
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨c + s * b ^ (q - 1) * c + (k : B) * ϖ ^ m' * c ^ 2, ?_, ?_⟩
  · exact S.add_mem (S.add_mem hc (S.mul_mem (S.mul_mem hs (S.pow_mem hb _)) hc))
      (S.mul_mem (S.mul_mem k.2 (S.pow_mem hϖ _)) (S.pow_mem hc _))
  · rw [ha, hk', hqs]; ring

theorem iter_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) (n : ℕ) :
    ∀ {a b c : B} {m : ℕ}, a ∈ S → b ∈ S → c ∈ S → 1 ≤ m → a - b = ϖ ^ m * c →
      ∃ c' ∈ S, ltIter ϖ q n a - ltIter ϖ q n b = ϖ ^ (m + n) * c' := by
  induction n with
  | zero =>
    intro a b c m _ _ hc _ hab
    exact ⟨c, hc, by simpa [ltIter] using hab⟩
  | succ n ih =>
    intro a b c m ha hb hc hm hab
    obtain ⟨c₁, hc₁, h₁⟩ := step_congr hϖ hq hb hc hm hab
    obtain ⟨c₂, hc₂, h₂⟩ := ih (map_mem hϖ q ha) (map_mem hϖ q hb) hc₁ (by omega) h₁
    refine ⟨c₂, hc₂, ?_⟩
    have e : m + (n + 1) = m + 1 + n := by omega
    rw [e]
    exact h₂

theorem exists_limit : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      ∃ Q ∈ S, ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a := by
  intro B _ S F ϖ E q _ hq v hv hvq
  have hd : ∀ n, ∃ e ∈ S, ltIter ϖ q (n + 1) (v (n + 1)) - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * e := by
    intro n
    have h1 : (ϖ * v (n + 1) + v (n + 1) ^ q) - v n = ϖ ^ 1 * v (n + 1) := by
      rw [hvq]; ring
    obtain ⟨c, hc, h⟩ := iter_congr E.mem hq n (map_mem E.mem q (hv (n + 1))) (hv n) (hv (n + 1))
      le_rfl h1
    refine ⟨c, hc, ?_⟩
    have e : ltIter ϖ q (n + 1) (v (n + 1)) = ltIter ϖ q n (ϖ * v (n + 1) + v (n + 1) ^ q) := rfl
    rw [e, h, add_comm n 1]
  choose e he hde using hd
  let s : ℕ → B := fun n => Nat.casesOn n (v 0) e
  have hs : ∀ n, s n ∈ S := by
    intro n
    cases n with
    | zero => exact hv 0
    | succ n => exact he n
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ N, ∑ n ∈ Finset.range (N + 1), ϖ ^ n * s n = ltIter ϖ q N (v N) := by
    intro N
    induction N with
    | zero => simp [s, ltIter]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hN : s (N + 1) = e N := rfl
      rw [hN, ← hde N]
      ring
  refine ⟨r, hr, fun n => ?_⟩
  obtain ⟨a, ha, h⟩ := hsum (n + 1)
  rw [tel n] at h
  exact ⟨a, ha, h⟩

end GlobalTheory.CompanionTheory.LTPer.QLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecsMapArrow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem secs_map_arrow {X : Scheme.{0}} {E : X.Modules} (D : Subobject E)
    (B : Subobject (D : X.Modules)) (V : X.Opens) :
    secs ((Subobject.map D.arrow).obj B) V = (D.arrow.app V) '' secs B V := by
  have hmk : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    exact Subobject.map_mk _ _
  let e := Subobject.isoOfEqMk _ _ hmk
  have he : e.hom ≫ (B.arrow ≫ D.arrow) = ((Subobject.map D.arrow).obj B).arrow := by
    simp only [e, Subobject.isoOfEqMk_hom, Subobject.ofLEMk_comp]
  have he' : e.inv ≫ ((Subobject.map D.arrow).obj B).arrow = B.arrow ≫ D.arrow := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext y
  simp only [GlobalTheory.CompanionTheory.GE.secs]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(B.arrow.app V) ((e.hom.app V) x), ⟨_, rfl⟩, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(e.inv.app V) x, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he'
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h

end GlobalTheory.CompanionTheory.GE
end

